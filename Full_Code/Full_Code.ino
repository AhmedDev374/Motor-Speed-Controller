// ESP32 closed-loop RPM control (v9)
//
// Pot sets TARGET RPM. The Hall sensor measures the REAL wheel RPM. The ESP32 changes the motor
// power (PWM on ENA) until real RPM = target RPM (goal: error under 2% in steady state).
//
// v9 quick calibration: about 8 s at every start (nothing is saved except p and x settings).
// What is new in v9:
//  - Strong noise rejection: a pulse must hold 2 ms, can not come faster than the maximum
//    plausible speed, and can not come faster than half of the previous interval.
//  - RPM = median of the last 3 intervals, so one fake pulse can not make a huge number.
//  - Calibration is rejected (and repeated) if its readings are not stable.
//  - The old 3% deadband is gone (it allowed 3% error). Now 0.3%.
//  - The controller updates on every NEW pulse, with an integral that converges to ~0 error.
//  - Pot is read more smoothly, so the target does not jump.
//
// Wiring (same as before):
//   Pot:   left -> 3.3V, middle -> D4 (GPIO4), right -> GND   (100 nF cap middle -> GND helps)
//   Hall:  VCC -> 3.3V, GND -> GND, OUT -> D18  (10k resistor from OUT to 3.3V)
//   LCD:   SDA -> D23, SCL -> D22, GND -> GND, VCC -> 5V (VIN)
//   L298N: IN1 -> D2, IN2 -> D15, ENA -> D5 (PWM = speed, REMOVE the ENA jumper cap)
//          battery + -> 12V/VS, battery - -> GND, ESP32 GND -> driver GND
//   Motor: 0.1 uF (104) ceramic capacitor across the two motor terminals.
// Needs ESP32 Arduino core 3.x and the "LiquidCrystal I2C" library. D4 is ADC2: no WiFi here.
//
// Serial Monitor commands (115200 baud):
//   c          recalibrate now
//   p<N>       pulses per wheel turn = number of magnets          (example: p1)
//   x<RPM>     maximum plausible RPM, about 1.3 x the real top RPM (example: x200)
//   t<seconds> seconds per ONE wheel turn from your stopwatch      (example: t0.4)
//   r<RPM>     the real RPM you measured                           (example: r150)

#include <Wire.h>
#include <LiquidCrystal_I2C.h>
#include <Preferences.h>

// ---------------- Pins ----------------
#define SDA_PIN 21
#define SCL_PIN 22
#define POT_PIN 4
#define HALL_PIN 18
#define IN1 2
#define IN2 15
#define ENA 5

// ---------------- Settings ----------------
#define LCD_COLS 16
#define LCD_ROWS 2

float pulsesPerRev = 1.0;           // number of magnets on the wheel (saved in flash)
float maxPlausibleRpm = 300;        // anything above this is noise (saved in flash, command x)

const bool INVERT_POT = true;       // set false if the speed goes the wrong way
const int POT_RAW_MIN = 80;
const int POT_RAW_MAX = 4000;

const int PWM_FREQ = 1000;
const int PWM_RES = 8;              // 0-255
const int MAX_DUTY = 255;
const int MIN_DUTY = 30;

const float HEADROOM = 0.85;        // pot full = 85% of the measured full-power RPM (spare power)
const float FALLBACK_MAX_RPM = 100; // only if calibration fails (auto-limit corrects it)
const float MIN_TARGET_RPM = 3;

// Start-up calibration
const int CAL_HIGH_DUTY = 255;
const int CAL_LOW_DUTY = 100;
const unsigned long CAL_SETTLE_MS = 1500;
const unsigned long CAL_MEASURE_MS = 5000;
const float CAL_MAX_SPREAD = 0.15;  // readings may differ by 15% at most, else it is noise

// Controller
const float KP_N = 0.10;            // proportional
const float KI_N = 0.80;            // integral per second (step is limited, see loop)
const float MAX_I_STEP = 0.50;      // max fraction of the error corrected per new pulse
const float DEADBAND_FRAC = 0.003;  // 0.3% deadband
const float SLEW_PER_S = 400;       // max duty change per second
const unsigned long SAT_TIME_MS = 3000;
const float STALL_RAMP_PER_S = 20;  // duty added per second while no pulses arrive (stuck motor)

// Hall sampling filter (timer reads the pin 4000x/s)
#define ACTIVE_LEVEL LOW
const unsigned long SAMPLE_US = 250;
const int MIN_SAMPLES = 8;          // pulse must hold 8 x 250 us = 2 ms
#define RING 64
const float MAX_AGE_S = 8.0;

const unsigned long CONTROL_MS = 100;
const unsigned long DISPLAY_MS = 500;

// ---------------- Globals ----------------
LiquidCrystal_I2C *lcd = nullptr;
Preferences prefs;
hw_timer_t *hallTimer = nullptr;

volatile uint32_t totalPulses = 0;
volatile uint32_t glitchCount = 0;      // blips shorter than 2 ms
volatile uint32_t rejectCount = 0;      // pulses rejected as too fast
volatile uint32_t lastPulseUs = 0;
volatile uint32_t lastIntervalUs = 0;
volatile uint32_t minIntervalUs = 100000;
volatile uint8_t rejectStreak = 0;
volatile bool havePulse = false;
volatile uint8_t activeSamples = 0;
volatile uint8_t inactiveSamples = 0;
volatile bool latched = false;
volatile uint32_t ring[RING];
volatile uint8_t ringIdx = 0;
volatile uint8_t ringCount = 0;

uint32_t lastTotalSeen = 0;
bool freshData = false;

float maxRpm = FALLBACK_MAX_RPM;
float kRpmPerDuty = 0.6;            // learned: RPM per duty unit
float d0 = 30;                      // learned: duty where the motor starts to turn

float realRpm = 0;
float rpmAvg = 0;
float dispReal = 0;
float targetRpm = 0;
float potFilt = 0;
float integ = 0;
float dutyOut = 0;
float realSum = 0;
int sampleCount = 0;
int skipPulses = 0;
bool motorWasOff = true;
unsigned long holdUntilMs = 0;
unsigned long satSince = 0;
float stallBoost = 0;
unsigned long kickUntilMs = 0;      // short power burst when starting from standstill
float kickDuty = 0;
float minRpm = 10;                  // lowest speed the motor can hold (learned in calibration)
bool potOn = false;                 // pot is above the "off" zone
bool wasTurning = false;            // motor was turning and then stopped = target below its floor

// Timer interrupt (every 250 us): debounced pulse detector with plausibility gate
void IRAM_ATTR hallSampleISR() {
  uint32_t now = micros();
  bool active = (digitalRead(HALL_PIN) == ACTIVE_LEVEL);
  if (!latched) {
    if (active) {
      if (activeSamples < 255) activeSamples++;
      if (activeSamples >= MIN_SAMPLES) {
        latched = true;
        activeSamples = 0;
        inactiveSamples = 0;

        bool ok = true;
        uint32_t dt = now - lastPulseUs;
        if (havePulse) {
          if (dt < minIntervalUs) ok = false;                          // faster than possible
          else if (lastIntervalUs > 0 && dt < (lastIntervalUs >> 1)) ok = false;  // less than half
        }
        if (ok) {
          if (havePulse) lastIntervalUs = dt;
          lastPulseUs = now;
          havePulse = true;
          rejectStreak = 0;
          ring[ringIdx] = now;
          ringIdx = (ringIdx + 1) % RING;
          if (ringCount < RING) ringCount++;
          totalPulses++;
        } else {
          rejectCount++;
          if (++rejectStreak >= 5) {      // gate got stuck: release it
            lastIntervalUs = 0;
            rejectStreak = 0;
          }
        }
      }
    } else {
      if (activeSamples > 0) glitchCount++;
      activeSamples = 0;
    }
  } else {
    if (!active) {
      if (++inactiveSamples >= MIN_SAMPLES) {
        latched = false;
        inactiveSamples = 0;
        activeSamples = 0;
      }
    } else {
      inactiveSamples = 0;
    }
  }
}

void updateMinInterval() {
  float us = 60000000.0f / (maxPlausibleRpm * pulsesPerRev);
  us = constrain(us, 5000.0f, 2000000.0f);
  minIntervalUs = (uint32_t)us;
}

byte findLcdAddress() {
  for (byte addr = 1; addr < 127; addr++) {
    Wire.beginTransmission(addr);
    if (Wire.endTransmission() == 0) return addr;
  }
  return 0;
}

void lcdLine(int row, const char *text) {
  if (!lcd) return;
  char line[17];
  snprintf(line, sizeof(line), "%-16s", text);
  lcd->setCursor(0, row);
  lcd->print(line);
}

void motorSet(float duty) {
  if (duty <= 0) {
    digitalWrite(IN1, LOW);
    digitalWrite(IN2, LOW);
    ledcWrite(ENA, 0);
    return;
  }
  digitalWrite(IN1, HIGH);                // forward only
  digitalWrite(IN2, LOW);
  ledcWrite(ENA, (int)constrain(duty, 0, MAX_DUTY));
}

uint32_t readTotal() {
  noInterrupts();
  uint32_t t = totalPulses;
  interrupts();
  return t;
}

void resetRing() {
  noInterrupts();
  ringCount = 0;
  havePulse = false;
  lastIntervalUs = 0;
  rejectStreak = 0;
  interrupts();
}

uint32_t median3(uint32_t a, uint32_t b, uint32_t c) {
  uint32_t lo = a < b ? a : b;
  uint32_t hi = a < b ? b : a;
  uint32_t m = c < hi ? c : hi;
  return lo > m ? lo : m;
}

// RPM from the median of the last 3 intervals between clean pulses
float currentRpm() {
  uint32_t buf[4];
  uint8_t cnt, idx;
  noInterrupts();
  cnt = ringCount;
  idx = ringIdx;
  int n = cnt < 4 ? cnt : 4;
  for (int i = 0; i < n; i++) buf[i] = ring[(idx + RING - 1 - i) % RING];   // buf[0] = newest
  interrupts();
  if (n < 2) return 0;

  uint32_t nowUs = micros();
  float ageS = (uint32_t)(nowUs - buf[0]) / 1000000.0f;
  if (ageS > MAX_AGE_S) return 0;

  uint32_t iv[3];
  int m = n - 1;
  for (int i = 0; i < m; i++) iv[i] = buf[i] - buf[i + 1];

  uint32_t med;
  if (m == 1) med = iv[0];
  else if (m == 2) med = (iv[0] + iv[1]) / 2;
  else {
    med = median3(iv[0], iv[1], iv[2]);
    // the newest interval reacts faster: use it (averaged with the median) when they agree within 20%
    uint32_t diff = iv[0] > med ? iv[0] - med : med - iv[0];
    if (diff * 5 < med) med = (iv[0] + med) / 2;
  }
  if (med == 0) return 0;

  float hz = 1000000.0f / (float)med;
  if (ageS > 1.5f / hz) hz = min(hz, 1.0f / ageS);   // slowing down: do not keep the old speed
  return hz * 60.0f / pulsesPerRev;
}

// ---------------- Quick calibration (about 8 s, saved in flash) ----------------
const float SWEEP_RATE = 32.0;                  // duty units per second while sweeping down
const unsigned long CAL_FULL_MIN_MS = 1200;     // let the motor reach full speed first
const unsigned long CAL_FULL_MAX_MS = 3500;
const unsigned long CAL_SWEEP_MAX_MS = 6500;
#define CAL_MAX_POINTS 40

// Newest pulse time and the gap to the pulse before it
bool lastPulseInterval(uint32_t &tNewUs, uint32_t &dtUs) {
  uint32_t a, b;
  noInterrupts();
  if (ringCount < 2) {
    interrupts();
    return false;
  }
  a = ring[(ringIdx + RING - 1) % RING];
  b = ring[(ringIdx + RING - 2) % RING];
  interrupts();
  tNewUs = a;
  dtUs = a - b;
  return dtUs > 0;
}

float intervalRpm(uint32_t dtUs) {
  return 60000000.0f / ((float)dtUs * pulsesPerRev);
}

void calibrate() {
  Serial.println("Quick calibration: about 8 seconds. Keep the wheel free.");
  lcdLine(0, "Calibrating...");
  lcdLine(1, "keep wheel free");

  // Phase A: full power, measure the top speed from 3 clean pulse intervals
  float rpmHigh = 0;
  for (int tries = 0; tries < 2 && rpmHigh <= 0; tries++) {
    motorSet(CAL_HIGH_DUTY);
    resetRing();
    float hv[4];
    int hn = 0;
    uint32_t lastTot = readTotal();
    unsigned long t0 = millis();
    while (millis() - t0 < CAL_FULL_MAX_MS && hn < 3) {
      delay(10);
      uint32_t tot = readTotal();
      if (tot != lastTot) {
        lastTot = tot;
        uint32_t tn, dt;
        if (millis() - t0 >= CAL_FULL_MIN_MS && lastPulseInterval(tn, dt)) hv[hn++] = intervalRpm(dt);
      }
    }
    if (hn >= 2) {
      float lo = hv[0], hi = hv[0], sum = 0;
      for (int i = 0; i < hn; i++) {
        sum += hv[i];
        if (hv[i] < lo) lo = hv[i];
        if (hv[i] > hi) hi = hv[i];
      }
      float mean = sum / hn;
      if ((hi - lo) <= 0.25f * mean) rpmHigh = mean;
      else Serial.println("  full-power readings not stable (noise), retrying");
    }
  }
  Serial.print("  full power: ");
  Serial.print(rpmHigh, 1);
  Serial.println(" RPM");

  // Phase B: lower the power smoothly until the motor stalls; every pulse gives one (power, RPM) point
  float dutyPts[CAL_MAX_POINTS], rpmPts[CAL_MAX_POINTS];
  int np = 0;
  bool stalled = false;
  if (rpmHigh >= 10) {
    lcdLine(1, "finding min RPM");
    uint32_t sweepStartUs = micros();
    unsigned long s0 = millis();
    unsigned long lastSeenMs = s0;
    float lastDtS = 0;
    uint32_t lastTot = readTotal();
    while (millis() - s0 < CAL_SWEEP_MAX_MS) {
      delay(10);
      float duty = CAL_HIGH_DUTY - SWEEP_RATE * (millis() - s0) / 1000.0f;
      if (duty < 35) break;
      motorSet(duty);
      uint32_t tot = readTotal();
      if (tot != lastTot) {
        lastTot = tot;
        uint32_t tn, dt;
        if (lastPulseInterval(tn, dt)) {
          float r = intervalRpm(dt);
          // the interval is an average over its own time span: pair it with the power at its middle
          float tMid = (float)(int32_t)((tn - dt / 2) - sweepStartUs) / 1000000.0f;
          float d = constrain(CAL_HIGH_DUTY - SWEEP_RATE * tMid, 0.0f, 255.0f);
          if (r <= rpmHigh * 1.3f && np < CAL_MAX_POINTS) {
            dutyPts[np] = d;
            rpmPts[np] = r;
            np++;
          }
          lastDtS = dt / 1000000.0f;
          lastSeenMs = millis();
        }
      }
      if (np >= 3 && (millis() - lastSeenMs) / 1000.0f > fmaxf(1.6f * lastDtS, 0.8f)) {
        stalled = true;
        break;
      }
    }
  }
  motorSet(0);

  // Slowest speed the motor held. The last interval before a stall is the "dying" one: skip it.
  float floorRpm = 0;
  if (np >= 2) {
    int lastIdx = stalled ? np - 2 : np - 1;
    int firstIdx = max(0, lastIdx - 1);
    float s = 0;
    int c = 0;
    for (int i = firstIdx; i <= lastIdx; i++) {
      s += rpmPts[i];
      c++;
    }
    floorRpm = s / c;
  }

  // Straight-line fit of RPM against power (linear part only) -> k and d0
  float kFit = 0, d0Fit = 0;
  bool fitOk = false;
  if (rpmHigh >= 10) {
    double n = 1, sx = CAL_HIGH_DUTY, sy = rpmHigh;
    double sxx = (double)CAL_HIGH_DUTY * CAL_HIGH_DUTY, sxy = (double)CAL_HIGH_DUTY * rpmHigh;
    int lim = stalled ? np - 1 : np;
    for (int i = 0; i < lim; i++) {
      if (rpmPts[i] < 0.3f * rpmHigh) continue;
      n += 1;
      sx += dutyPts[i];
      sy += rpmPts[i];
      sxx += (double)dutyPts[i] * dutyPts[i];
      sxy += (double)dutyPts[i] * rpmPts[i];
    }
    double den = n * sxx - sx * sx;
    if (n >= 4 && den > 1.0) {
      double slope = (n * sxy - sx * sy) / den;
      double inter = (sy - slope * sx) / n;
      if (slope > 0.05 && slope < 20) {
        kFit = (float)slope;
        d0Fit = (float)(-inter / slope);
        fitOk = true;
      }
    }
  }

  if (rpmHigh >= 10) {
    maxRpm = min(rpmHigh * HEADROOM, maxPlausibleRpm);
    if (fitOk && d0Fit >= 0 && d0Fit <= 120) {
      kRpmPerDuty = kFit;
      d0 = d0Fit;
    } else {
      d0 = fitOk ? constrain(d0Fit, 0.0f, 120.0f) : 30.0f;
      kRpmPerDuty = rpmHigh / (float)(CAL_HIGH_DUTY - d0);
    }
    // lowest usable speed = slowest speed it really held + 15% safety
    minRpm = (floorRpm >= 3) ? max(5.0f, floorRpm * 1.15f) : 0.3f * maxRpm;
    if (minRpm > 0.85f * maxRpm) {
      // the motor can not run slowly: keep a usable pot range above the real floor
      maxRpm = min(min(max(maxRpm, minRpm * 1.3f), rpmHigh * 0.97f), maxPlausibleRpm);
      Serial.println("WARNING: the motor can not run slowly (narrow speed range). A better driver or a higher supply voltage widens it.");
    }
    minRpm = min(minRpm, 0.95f * maxRpm);
    Serial.print("Calibration OK. Full-power RPM: ");
    Serial.print(rpmHigh, 0);
    Serial.print(" | Slowest held: ");
    Serial.print(floorRpm, 0);
    Serial.print(" | Points: ");
    Serial.print(np);
    Serial.print(" | Max RPM at full pot: ");
    Serial.print(maxRpm, 0);
    Serial.print(" | k = ");
    Serial.print(kRpmPerDuty, 3);
    Serial.print(" | d0 = ");
    Serial.print(d0, 0);
    Serial.print(" | Min RPM: ");
    Serial.println(minRpm, 0);
  } else {
    maxRpm = FALLBACK_MAX_RPM;
    minRpm = 0.3f * maxRpm;
    d0 = 30;
    kRpmPerDuty = maxRpm / (float)(MAX_DUTY - d0);
    Serial.println("Calibration FAILED (no clean stable pulses). Check sensor wiring/magnet. Using fallback.");
  }

  char line[20];
  snprintf(line, sizeof(line), "Min:%d Max:%d", (int)minRpm, (int)maxRpm);
  lcdLine(0, "Calibration done");
  lcdLine(1, line);
  delay(600);
  resetRing();
  realRpm = 0;
  rpmAvg = 0;
  dispReal = 0;
  integ = 0;
  satSince = 0;
}

float readPotFrac() {
  long sum = 0;
  for (int i = 0; i < 64; i++) sum += analogRead(POT_PIN);
  float raw = sum / 64.0;
  if (INVERT_POT) raw = 4095.0 - raw;
  float frac = (raw - POT_RAW_MIN) / (float)(POT_RAW_MAX - POT_RAW_MIN);
  return constrain(frac, 0.0f, 1.0f);
}

// Pot mapping: bottom 4% of the pot = motor OFF (with hysteresis),
// the rest maps linearly from minRpm (lowest speed the motor can hold) to maxRpm.
float potToRpm(float f) {
  if (potOn) {
    if (f < 0.03f) potOn = false;
  } else if (f > 0.05f) {
    potOn = true;
  }
  if (!potOn) return 0;
  float x = constrain((f - 0.04f) / 0.96f, 0.0f, 1.0f);
  return minRpm + x * (maxRpm - minRpm);
}

void updateTarget() {
  potFilt = 0.9 * potFilt + 0.1 * readPotFrac();   // potFilt is now the pot position 0..1
  float cand = potToRpm(potFilt);
  if (fabs(cand - targetRpm) >= 1.5) {
    float newT = constrain(round(cand), 0.0f, maxRpm);
    if (targetRpm >= MIN_TARGET_RPM && fabs(newT - targetRpm) > 0.03f * targetRpm) skipPulses = 1;
    targetRpm = newT;
  }
  if (targetRpm > maxRpm) targetRpm = maxRpm;
}

void updateRealRpm() {
  uint32_t tot = readTotal();
  freshData = (tot != lastTotalSeen);
  lastTotalSeen = tot;

  float rpmNow = currentRpm();
  if (freshData) realRpm = rpmNow;
  else if (rpmNow < realRpm) realRpm = rpmNow;     // slowing down or stopped
  if (realRpm < 0.5) realRpm = 0;
  rpmAvg = 0.97 * rpmAvg + 0.03 * realRpm;
}

float errorPercent(float real) {
  if (targetRpm < MIN_TARGET_RPM) return 0;
  return fabs(real - targetRpm) * 100.0 / targetRpm;
}

void updateLcd() {
  char line[24];
  snprintf(line, sizeof(line), "Target RPM:%d", (int)targetRpm);
  lcdLine(0, line);

  if (targetRpm >= MIN_TARGET_RPM) {
    snprintf(line, sizeof(line), "R_RPM:%d E:%d%%",
             (int)round(dispReal), (int)round(errorPercent(dispReal)));
  } else {
    snprintf(line, sizeof(line), "R_RPM:%d E:--", (int)round(dispReal));
  }
  lcdLine(1, line);
}

void handleSerial() {
  while (Serial.available()) {
    char c = Serial.read();
    if (c == 'c' || c == 'C') {
      Serial.println("Recalibrating...");
      calibrate();
      motorWasOff = true;
    } else if (c == 'p' || c == 'P') {
      float v = Serial.parseFloat();
      if (v >= 0.5 && v <= 1000) {
        pulsesPerRev = v;
        prefs.putFloat("ppr9", v);
        updateMinInterval();
        Serial.print("Pulses per turn set to ");
        Serial.print(v, 2);
        Serial.println(" (saved). Recalibrating...");
        calibrate();
        motorWasOff = true;
      }
    } else if (c == 'x' || c == 'X') {
      float v = Serial.parseFloat();
      if (v >= 5 && v <= 5000) {
        maxPlausibleRpm = v;
        prefs.putFloat("mx9", v);
        updateMinInterval();
        Serial.print("Max plausible RPM set to ");
        Serial.print(v, 0);
        Serial.println(" (saved). Recalibrating...");
        calibrate();
        motorWasOff = true;
      }
    } else if (c == 'r' || c == 'R' || c == 't' || c == 'T') {
      bool isTime = (c == 't' || c == 'T');
      float v = Serial.parseFloat();
      float measured = isTime ? (v > 0 ? 60.0 / v : 0) : v;
      if (measured >= 1 && rpmAvg > 0.5) {
        float newPpr = pulsesPerRev * rpmAvg / measured;
        if (newPpr >= 0.5 && newPpr <= 1000) {
          Serial.print("Sketch showed ");
          Serial.print(rpmAvg, 1);
          Serial.print(" RPM, you measured ");
          Serial.print(measured, 1);
          Serial.print(" RPM -> pulses per turn = ");
          Serial.print(newPpr, 2);
          Serial.println(" (saved). Recalibrating...");
          pulsesPerRev = newPpr;
          prefs.putFloat("ppr9", newPpr);
          updateMinInterval();
          calibrate();
          motorWasOff = true;
        }
      } else {
        Serial.println("Nothing changed: the motor must be turning steadily first.");
      }
    }
  }
}

void setup() {
  Serial.begin(115200);
  delay(500);

  prefs.begin("rpm", false);

  pulsesPerRev = prefs.getFloat("ppr9", 1.0);
  maxPlausibleRpm = prefs.getFloat("mx9", 300);
  updateMinInterval();
  Serial.print("Pulses per turn in use: ");
  Serial.println(pulsesPerRev, 2);
  Serial.print("Max plausible RPM: ");
  Serial.println(maxPlausibleRpm, 0);

  pinMode(IN1, OUTPUT);
  pinMode(IN2, OUTPUT);
  ledcAttach(ENA, PWM_FREQ, PWM_RES);
  motorSet(0);

  analogReadResolution(12);
  pinMode(POT_PIN, INPUT);

  pinMode(HALL_PIN, INPUT_PULLUP);
  hallTimer = timerBegin(1000000);
  timerAttachInterrupt(hallTimer, &hallSampleISR);
  timerAlarm(hallTimer, SAMPLE_US, true, 0);

  Wire.begin(SDA_PIN, SCL_PIN);
  byte addr = findLcdAddress();
  if (addr == 0) {
    Serial.println("LCD not found, check SDA/SCL/VCC/GND. Continuing without LCD.");
  } else {
    lcd = new LiquidCrystal_I2C(addr, LCD_COLS, LCD_ROWS);
    delay(500);
    lcd->init();
    delay(100);
    lcd->backlight();
    lcdLine(0, "RPM controller");
    lcdLine(1, "Starting...");
    delay(1000);
  }

  calibrate();

  potFilt = readPotFrac();
  targetRpm = round(potToRpm(potFilt));
  if (lcd) lcd->clear();
}

void loop() {
  static unsigned long lastControl = 0;
  static unsigned long lastDisplay = 0;
  static unsigned long lastFreshMs = 0;
  unsigned long now = millis();

  handleSerial();

  if (now - lastControl >= CONTROL_MS) {
    float dt = (now - lastControl) / 1000.0;
    lastControl = now;

    updateTarget();
    updateRealRpm();
    float freshDt = 0;
    if (freshData) {
      freshDt = (now - lastFreshMs) / 1000.0;
      lastFreshMs = now;
    }

    if (targetRpm < MIN_TARGET_RPM) {
      integ = 0;
      dutyOut = 0;
      satSince = 0;
      motorSet(0);
      motorWasOff = true;
      stallBoost = 0;
      wasTurning = false;
      lastFreshMs = now;
    } else {
      // Feed-forward: duty the learned motor curve says is needed
      float ff = constrain(d0 + targetRpm / kRpmPerDuty, (float)MIN_DUTY, (float)MAX_DUTY);

      if (motorWasOff) {
        motorWasOff = false;
        integ = 0;
        dutyOut = ff;
        kickDuty = fminf(ff + 70.0f, (float)MAX_DUTY);
        kickUntilMs = now + 250;
        skipPulses = 1;
        holdUntilMs = now + 500;
      }

      float rawErr = targetRpm - realRpm;
      float deadband = DEADBAND_FRAC * targetRpm;
      float err = rawErr;
      if (fabs(err) < deadband || now < holdUntilMs) err = 0;

      // integral moves only when a NEW pulse arrived (new measurement)
      if (freshData) {
        if (skipPulses > 0) {
          skipPulses--;
        } else {
          float g = fminf(KI_N * freshDt, MAX_I_STEP);
          integ += g * (err / kRpmPerDuty);
        }
      }

      // Stall recovery: no pulse for too long -> motor is stuck or too slow, add power with TIME
      float expectedS = 60.0f / (targetRpm * pulsesPerRev);
      float sinceFreshS = (now - lastFreshMs) / 1000.0f;
      if (freshData) wasTurning = true;
      // It was turning and then stopped for a long time: this target is below what the motor can hold
      if (!freshData && wasTurning && sinceFreshS > fmaxf(2.5f * expectedS, 1.5f)) {
        wasTurning = false;
        minRpm = min(max(minRpm, targetRpm * 1.15f), 0.9f * maxRpm);
        Serial.print("Motor stalled at target ");
        Serial.print(targetRpm, 0);
        Serial.print(". New min RPM: ");
        Serial.println(minRpm, 0);
      }
      if (!freshData && sinceFreshS > fmaxf(1.5f * expectedS, 1.0f)) {
        float add = STALL_RAMP_PER_S * dt;
        integ += add;
        stallBoost += add;
      } else if (freshData && stallBoost > 0) {
        integ -= 0.7f * stallBoost;     // running needs less power than starting
        stallBoost = 0;
      }
      integ = constrain(integ, -0.5f * MAX_DUTY, 0.5f * MAX_DUTY);

      float desired = ff + KP_N * (err / kRpmPerDuty) + integ;
      desired = constrain(desired, (float)MIN_DUTY, (float)MAX_DUTY);

      float maxStep = SLEW_PER_S * dt;
      if (desired > dutyOut + maxStep) desired = dutyOut + maxStep;
      else if (desired < dutyOut - maxStep) desired = dutyOut - maxStep;
      dutyOut = desired;

      // Auto-limit: full power but still too slow for 3 s -> lower max RPM to reality
      if (dutyOut >= MAX_DUTY - 1 && rawErr > fmaxf(2.0f, deadband) && now > holdUntilMs && realRpm > 5) {
        if (satSince == 0) satSince = now;
        else if (now - satSince > SAT_TIME_MS) {
          maxRpm = max(10.0f, realRpm * 0.98f);
          minRpm = min(minRpm, 0.8f * maxRpm);
          kRpmPerDuty = realRpm / (float)(MAX_DUTY - d0);
          targetRpm = min(targetRpm, maxRpm);
          integ = 0;
          satSince = 0;
          holdUntilMs = now + 2000;
          Serial.print("Target not reachable. New max RPM: ");
          Serial.println(maxRpm, 0);
        }
      } else {
        satSince = 0;
      }

      if (now < kickUntilMs) motorSet(fmaxf(dutyOut, kickDuty));
      else motorSet(dutyOut);
    }

    realSum += realRpm;
    sampleCount++;
  }

  if (now - lastDisplay >= DISPLAY_MS && sampleCount > 0) {
    lastDisplay = now;
    float avg = realSum / sampleCount;
    dispReal = (dispReal == 0 || avg == 0) ? avg : 0.5f * dispReal + 0.5f * avg;
    realSum = 0;
    sampleCount = 0;

    Serial.print("Target RPM: ");
    Serial.print(targetRpm, 0);
    Serial.print(" | Real RPM: ");
    Serial.print(dispReal, 1);
    Serial.print(" | Duty: ");
    Serial.print(dutyOut, 0);
    Serial.print(" | Max RPM: ");
    Serial.print(maxRpm, 0);
    Serial.print(" | Pulses: ");
    Serial.print(readTotal());
    Serial.print(" | Noise blocked: ");
    Serial.print(glitchCount + rejectCount);
    Serial.print(" | Error: ");
    if (targetRpm >= MIN_TARGET_RPM) {
      Serial.print(errorPercent(dispReal), 1);
      Serial.println(" %");
    } else {
      Serial.println("--");
    }

    if (lcd) updateLcd();
  }
}
