-- Prove2me | solution 1 for WorkbookSource.base_47449
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:15:57.602867+00:00
-- url     : https://prove2.me/submissions/c45154fe-0282-456f-8133-a2a2c8f72c62

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 - b * c + a)^2 / (b^2 + c^2) + (b^2 - c * a + b)^2 / (c^2 + a^2) + (c^2 - a * b + c)^2 / (a^2 + b^2) ≥ 3 / 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^8 + 4*a^7 + 2*a^6*b^2 - 4*a^6*b*c + 2*a^6*c^2 + 2*a^6 + 4*a^5*b^2 - 4*a^5*b*c + 4*a^5*c^2 + 2*a^4*b^4 - 4*a^4*b^3*c + 8*a^4*b^2*c^2 - a^4*b^2 - 4*a^4*b*c^3 + 2*a^4*c^4 - a^4*c^2 - 4*a^3*b^4*c - 4*a^3*b^3*c^2 - 12*a^3*b^3*c - 4*a^3*b^2*c^3 + 4*a^3*b^2*c^2 - 4*a^3*b*c^4 - 12*a^3*b*c^3 + 2*a^2*b^6 + 4*a^2*b^5 + 8*a^2*b^4*c^2 - a^2*b^4 - 4*a^2*b^3*c^3 + 4*a^2*b^3*c^2 + 8*a^2*b^2*c^4 + 4*a^2*b^2*c^3 + 2*a^2*c^6 + 4*a^2*c^5 - a^2*c^4 - 4*a*b^6*c - 4*a*b^5*c - 4*a*b^4*c^3 - 4*a*b^3*c^4 - 12*a*b^3*c^3 - 4*a*b*c^6 - 4*a*b*c^5 + 2*b^8 + 4*b^7 + 2*b^6*c^2 + 2*b^6 + 4*b^5*c^2 + 2*b^4*c^4 - b^4*c^2 + 2*b^2*c^6 + 4*b^2*c^5 - b^2*c^4 + 2*c^8 + 4*c^7 + 2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (48 : ℝ) * a^6 * (b - a)^2 + (48 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (48 : ℝ) * a^6 * (c - b)^2 + (176 : ℝ) * a^5 * (b - a)^3 + (264 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (80 : ℝ) * a^5 * (b - a)^2 + (312 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (80 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (112 : ℝ) * a^5 * (c - b)^3 + (80 : ℝ) * a^5 * (c - b)^2 + (304 : ℝ) * a^4 * (b - a)^4 + (608 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (240 : ℝ) * a^4 * (b - a)^3 + (872 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (360 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (16 : ℝ) * a^4 * (b - a)^2 + (568 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (440 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (16 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (144 : ℝ) * a^4 * (c - b)^4 + (160 : ℝ) * a^4 * (c - b)^3 + (16 : ℝ) * a^4 * (c - b)^2 + (304 : ℝ) * a^3 * (b - a)^5 + (760 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (320 : ℝ) * a^3 * (b - a)^4 + (1296 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (640 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (32 : ℝ) * a^3 * (b - a)^3 + (1184 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (960 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (48 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (568 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (640 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (80 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (112 : ℝ) * a^3 * (c - b)^5 + (160 : ℝ) * a^3 * (c - b)^4 + (32 : ℝ) * a^3 * (c - b)^3 + (184 : ℝ) * a^2 * (b - a)^6 + (552 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (232 : ℝ) * a^2 * (b - a)^5 + (1094 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (580 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (28 : ℝ) * a^2 * (b - a)^4 + (1268 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (1032 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (56 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (878 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (968 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (132 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (336 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (460 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (104 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (56 : ℝ) * a^2 * (c - b)^6 + (88 : ℝ) * a^2 * (c - b)^5 + (28 : ℝ) * a^2 * (c - b)^4 + (64 : ℝ) * a^1 * (b - a)^7 + (224 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (92 : ℝ) * a^1 * (b - a)^6 + (504 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (276 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (12 : ℝ) * a^1 * (b - a)^5 + (700 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (564 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (30 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (624 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (668 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (92 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (348 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (460 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (108 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (112 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (172 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (58 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (16 : ℝ) * a^1 * (c - b)^7 + (28 : ℝ) * a^1 * (c - b)^6 + (12 : ℝ) * a^1 * (c - b)^5 + (10 : ℝ) * (b - a)^8 + (40 : ℝ) * (b - a)^7 * (c - b)^1 + (16 : ℝ) * (b - a)^7 + (100 : ℝ) * (b - a)^6 * (c - b)^2 + (56 : ℝ) * (b - a)^6 * (c - b)^1 + (2 : ℝ) * (b - a)^6 + (160 : ℝ) * (b - a)^5 * (c - b)^3 + (128 : ℝ) * (b - a)^5 * (c - b)^2 + (6 : ℝ) * (b - a)^5 * (c - b)^1 + (172 : ℝ) * (b - a)^4 * (c - b)^4 + (180 : ℝ) * (b - a)^4 * (c - b)^3 + (23 : ℝ) * (b - a)^4 * (c - b)^2 + (124 : ℝ) * (b - a)^3 * (c - b)^5 + (160 : ℝ) * (b - a)^3 * (c - b)^4 + (36 : ℝ) * (b - a)^3 * (c - b)^3 + (58 : ℝ) * (b - a)^2 * (c - b)^6 + (88 : ℝ) * (b - a)^2 * (c - b)^5 + (29 : ℝ) * (b - a)^2 * (c - b)^4 + (16 : ℝ) * (b - a)^1 * (c - b)^7 + (28 : ℝ) * (b - a)^1 * (c - b)^6 + (12 : ℝ) * (b - a)^1 * (c - b)^5 + (2 : ℝ) * (c - b)^8 + (4 : ℝ) * (c - b)^7 + (2 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^8 + 4*a^7 + 2*a^6*b^2 - 4*a^6*b*c + 2*a^6*c^2 + 2*a^6 + 4*a^5*b^2 - 4*a^5*b*c + 4*a^5*c^2 + 2*a^4*b^4 - 4*a^4*b^3*c + 8*a^4*b^2*c^2 - a^4*b^2 - 4*a^4*b*c^3 + 2*a^4*c^4 - a^4*c^2 - 4*a^3*b^4*c - 4*a^3*b^3*c^2 - 12*a^3*b^3*c - 4*a^3*b^2*c^3 + 4*a^3*b^2*c^2 - 4*a^3*b*c^4 - 12*a^3*b*c^3 + 2*a^2*b^6 + 4*a^2*b^5 + 8*a^2*b^4*c^2 - a^2*b^4 - 4*a^2*b^3*c^3 + 4*a^2*b^3*c^2 + 8*a^2*b^2*c^4 + 4*a^2*b^2*c^3 + 2*a^2*c^6 + 4*a^2*c^5 - a^2*c^4 - 4*a*b^6*c - 4*a*b^5*c - 4*a*b^4*c^3 - 4*a*b^3*c^4 - 12*a*b^3*c^3 - 4*a*b*c^6 - 4*a*b*c^5 + 2*b^8 + 4*b^7 + 2*b^6*c^2 + 2*b^6 + 4*b^5*c^2 + 2*b^4*c^4 - b^4*c^2 + 2*b^2*c^6 + 4*b^2*c^5 - b^2*c^4 + 2*c^8 + 4*c^7 + 2*c^6) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux0 a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux0 b a c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux0 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c b a (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (2*a^8 + 4*a^7 + 2*a^6*b^2 - 4*a^6*b*c + 2*a^6*c^2 + 2*a^6 + 4*a^5*b^2 - 4*a^5*b*c + 4*a^5*c^2 + 2*a^4*b^4 - 4*a^4*b^3*c + 8*a^4*b^2*c^2 - a^4*b^2 - 4*a^4*b*c^3 + 2*a^4*c^4 - a^4*c^2 - 4*a^3*b^4*c - 4*a^3*b^3*c^2 - 12*a^3*b^3*c - 4*a^3*b^2*c^3 + 4*a^3*b^2*c^2 - 4*a^3*b*c^4 - 12*a^3*b*c^3 + 2*a^2*b^6 + 4*a^2*b^5 + 8*a^2*b^4*c^2 - a^2*b^4 - 4*a^2*b^3*c^3 + 4*a^2*b^3*c^2 + 8*a^2*b^2*c^4 + 4*a^2*b^2*c^3 + 2*a^2*c^6 + 4*a^2*c^5 - a^2*c^4 - 4*a*b^6*c - 4*a*b^5*c - 4*a*b^4*c^3 - 4*a*b^3*c^4 - 12*a*b^3*c^3 - 4*a*b*c^6 - 4*a*b*c^5 + 2*b^8 + 4*b^7 + 2*b^6*c^2 + 2*b^6 + 4*b^5*c^2 + 2*b^4*c^4 - b^4*c^2 + 2*b^2*c^6 + 4*b^2*c^5 - b^2*c^4 + 2*c^8 + 4*c^7 + 2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 - b * c + a)^2 / (b^2 + c^2) + (b^2 - c * a + b)^2 / (c^2 + a^2) + (c^2 - a * b + c)^2 / (a^2 + b^2) ≥ 3 / 2) := @solution
#print axioms solution
