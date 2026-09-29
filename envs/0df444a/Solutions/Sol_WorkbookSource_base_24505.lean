-- Prove2me | solution 1 for WorkbookSource.base_24505
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:02:13.289253+00:00
-- url     : https://prove2.me/submissions/e6efc8ee-5955-471b-86b3-02a4b705b95e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (1 / a + 1 / (b + c) + 1 / (a + b + c)) + b / (1 / b + 1 / (c + a) + 1 / (a + b + c)) + c / (1 / c + 1 / (a + b) + 1 / (a + b + c))) ≥ (6 / 11) * (a * b + b * c + c * a)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (5*a^7*b + 5*a^7*c + 29*a^6*b^2 + 30*a^6*b*c + 29*a^6*c^2 + 65*a^5*b^3 + 52*a^5*b^2*c + 52*a^5*b*c^2 + 65*a^5*c^3 + 82*a^4*b^4 + 23*a^4*b^3*c - 136*a^4*b^2*c^2 + 23*a^4*b*c^3 + 82*a^4*c^4 + 65*a^3*b^5 + 23*a^3*b^4*c - 324*a^3*b^3*c^2 - 324*a^3*b^2*c^3 + 23*a^3*b*c^4 + 65*a^3*c^5 + 29*a^2*b^6 + 52*a^2*b^5*c - 136*a^2*b^4*c^2 - 324*a^2*b^3*c^3 - 136*a^2*b^2*c^4 + 52*a^2*b*c^5 + 29*a^2*c^6 + 5*a*b^7 + 30*a*b^6*c + 52*a*b^5*c^2 + 23*a*b^4*c^3 + 23*a*b^3*c^4 + 52*a*b^2*c^5 + 30*a*b*c^6 + 5*a*c^7 + 5*b^7*c + 29*b^6*c^2 + 65*b^5*c^3 + 82*b^4*c^4 + 65*b^3*c^5 + 29*b^2*c^6 + 5*b*c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (2464 : ℝ) * a^6 * (b - a)^2 + (2464 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (2464 : ℝ) * a^6 * (c - b)^2 + (10510 : ℝ) * a^5 * (b - a)^3 + (15765 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (13803 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (4274 : ℝ) * a^5 * (c - b)^3 + (18504 : ℝ) * a^4 * (b - a)^4 + (37008 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (35017 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (16513 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (2914 : ℝ) * a^4 * (c - b)^4 + (17224 : ℝ) * a^3 * (b - a)^5 + (43060 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (47076 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (27554 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (8258 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (972 : ℝ) * a^3 * (c - b)^5 + (8946 : ℝ) * a^2 * (b - a)^6 + (26838 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (34291 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (23852 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (9385 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (1932 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (158 : ℝ) * a^2 * (c - b)^6 + (2460 : ℝ) * a^1 * (b - a)^7 + (8610 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (12770 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (10400 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (4976 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (1369 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (193 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (10 : ℝ) * a^1 * (c - b)^7 + (280 : ℝ) * (b - a)^8 + (1120 : ℝ) * (b - a)^7 * (c - b)^1 + (1906 : ℝ) * (b - a)^6 * (c - b)^2 + (1798 : ℝ) * (b - a)^5 * (c - b)^3 + (1017 : ℝ) * (b - a)^4 * (c - b)^4 + (344 : ℝ) * (b - a)^3 * (c - b)^5 + (64 : ℝ) * (b - a)^2 * (c - b)^6 + (5 : ℝ) * (b - a)^1 * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (5*a^7*b + 5*a^7*c + 29*a^6*b^2 + 30*a^6*b*c + 29*a^6*c^2 + 65*a^5*b^3 + 52*a^5*b^2*c + 52*a^5*b*c^2 + 65*a^5*c^3 + 82*a^4*b^4 + 23*a^4*b^3*c - 136*a^4*b^2*c^2 + 23*a^4*b*c^3 + 82*a^4*c^4 + 65*a^3*b^5 + 23*a^3*b^4*c - 324*a^3*b^3*c^2 - 324*a^3*b^2*c^3 + 23*a^3*b*c^4 + 65*a^3*c^5 + 29*a^2*b^6 + 52*a^2*b^5*c - 136*a^2*b^4*c^2 - 324*a^2*b^3*c^3 - 136*a^2*b^2*c^4 + 52*a^2*b*c^5 + 29*a^2*c^6 + 5*a*b^7 + 30*a*b^6*c + 52*a*b^5*c^2 + 23*a*b^4*c^3 + 23*a*b^3*c^4 + 52*a*b^2*c^5 + 30*a*b*c^6 + 5*a*c^7 + 5*b^7*c + 29*b^6*c^2 + 65*b^5*c^3 + 82*b^4*c^4 + 65*b^3*c^5 + 29*b^2*c^6 + 5*b*c^7) := by
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
  have hn : 0 ≤ (5*a^7*b + 5*a^7*c + 29*a^6*b^2 + 30*a^6*b*c + 29*a^6*c^2 + 65*a^5*b^3 + 52*a^5*b^2*c + 52*a^5*b*c^2 + 65*a^5*c^3 + 82*a^4*b^4 + 23*a^4*b^3*c - 136*a^4*b^2*c^2 + 23*a^4*b*c^3 + 82*a^4*c^4 + 65*a^3*b^5 + 23*a^3*b^4*c - 324*a^3*b^3*c^2 - 324*a^3*b^2*c^3 + 23*a^3*b*c^4 + 65*a^3*c^5 + 29*a^2*b^6 + 52*a^2*b^5*c - 136*a^2*b^4*c^2 - 324*a^2*b^3*c^3 - 136*a^2*b^2*c^4 + 52*a^2*b*c^5 + 29*a^2*c^6 + 5*a*b^7 + 30*a*b^6*c + 52*a*b^5*c^2 + 23*a*b^4*c^3 + 23*a*b^3*c^4 + 52*a*b^2*c^5 + 30*a*b*c^6 + 5*a*c^7 + 5*b^7*c + 29*b^6*c^2 + 65*b^5*c^3 + 82*b^4*c^4 + 65*b^3*c^5 + 29*b^2*c^6 + 5*b*c^7) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / (1 / a + 1 / (b + c) + 1 / (a + b + c)) + b / (1 / b + 1 / (c + a) + 1 / (a + b + c)) + c / (1 / c + 1 / (a + b) + 1 / (a + b + c))) ≥ (6 / 11) * (a * b + b * c + c * a)) := @solution
#print axioms solution
