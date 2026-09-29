-- Prove2me | solution 1 for WorkbookSource.base_6317
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:19:08.943032+00:00
-- url     : https://prove2.me/submissions/27453d65-d76e-4464-9bd0-03be0161c246

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (a + b) + b / (b + c) + c / (c + a) + (9 * (a ^ 3 + b ^ 3 + c ^ 3)) / (a + b + c) ^ 3) ≥ 5 / 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (17*a^5*b + 15*a^5*c + 12*a^4*b^2 + 20*a^4*b*c + 8*a^4*c^2 - 12*a^3*b^3 - 19*a^3*b^2*c - 21*a^3*b*c^2 - 12*a^3*c^3 + 8*a^2*b^4 - 21*a^2*b^3*c - 60*a^2*b^2*c^2 - 19*a^2*b*c^3 + 12*a^2*c^4 + 15*a*b^5 + 20*a*b^4*c - 19*a*b^3*c^2 - 21*a*b^2*c^3 + 20*a*b*c^4 + 17*a*c^5 + 17*b^5*c + 12*b^4*c^2 - 12*b^3*c^3 + 8*b^2*c^4 + 15*b*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (288 : ℝ) * a^4 * (b - a)^2 + (288 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (288 : ℝ) * a^4 * (c - b)^2 + (736 : ℝ) * a^3 * (b - a)^3 + (1077 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (1173 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (416 : ℝ) * a^3 * (c - b)^3 + (680 : ℝ) * a^2 * (b - a)^4 + (1306 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (1623 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (997 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (200 : ℝ) * a^2 * (c - b)^4 + (272 : ℝ) * a^1 * (b - a)^5 + (644 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (904 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (739 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (271 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (32 : ℝ) * a^1 * (c - b)^5 + (40 : ℝ) * (b - a)^6 + (112 : ℝ) * (b - a)^5 * (c - b)^1 + (174 : ℝ) * (b - a)^4 * (c - b)^2 + (170 : ℝ) * (b - a)^3 * (c - b)^3 + (83 : ℝ) * (b - a)^2 * (c - b)^4 + (15 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (17*a^5*b + 15*a^5*c + 12*a^4*b^2 + 20*a^4*b*c + 8*a^4*c^2 - 12*a^3*b^3 - 19*a^3*b^2*c - 21*a^3*b*c^2 - 12*a^3*c^3 + 8*a^2*b^4 - 21*a^2*b^3*c - 60*a^2*b^2*c^2 - 19*a^2*b*c^3 + 12*a^2*c^4 + 15*a*b^5 + 20*a*b^4*c - 19*a*b^3*c^2 - 21*a*b^2*c^3 + 20*a*b*c^4 + 17*a*c^5 + 17*b^5*c + 12*b^4*c^2 - 12*b^3*c^3 + 8*b^2*c^4 + 15*b*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (288 : ℝ) * a^4 * (c - a)^2 + (288 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (288 : ℝ) * a^4 * (b - c)^2 + (736 : ℝ) * a^3 * (c - a)^3 + (1131 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (1227 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (416 : ℝ) * a^3 * (b - c)^3 + (680 : ℝ) * a^2 * (c - a)^4 + (1414 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (1785 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (1051 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (200 : ℝ) * a^2 * (b - c)^4 + (272 : ℝ) * a^1 * (c - a)^5 + (716 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (1048 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (829 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (289 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (32 : ℝ) * a^1 * (b - c)^5 + (40 : ℝ) * (c - a)^6 + (128 : ℝ) * (c - a)^5 * (b - c)^1 + (214 : ℝ) * (c - a)^4 * (b - c)^2 + (206 : ℝ) * (c - a)^3 * (b - c)^3 + (97 : ℝ) * (c - a)^2 * (b - c)^4 + (17 : ℝ) * (c - a)^1 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (17*a^5*b + 15*a^5*c + 12*a^4*b^2 + 20*a^4*b*c + 8*a^4*c^2 - 12*a^3*b^3 - 19*a^3*b^2*c - 21*a^3*b*c^2 - 12*a^3*c^3 + 8*a^2*b^4 - 21*a^2*b^3*c - 60*a^2*b^2*c^2 - 19*a^2*b*c^3 + 12*a^2*c^4 + 15*a*b^5 + 20*a*b^4*c - 19*a*b^3*c^2 - 21*a*b^2*c^3 + 20*a*b*c^4 + 17*a*c^5 + 17*b^5*c + 12*b^4*c^2 - 12*b^3*c^3 + 8*b^2*c^4 + 15*b*c^5) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux1 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux1 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux0 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux1 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (17*a^5*b + 15*a^5*c + 12*a^4*b^2 + 20*a^4*b*c + 8*a^4*c^2 - 12*a^3*b^3 - 19*a^3*b^2*c - 21*a^3*b*c^2 - 12*a^3*c^3 + 8*a^2*b^4 - 21*a^2*b^3*c - 60*a^2*b^2*c^2 - 19*a^2*b*c^3 + 12*a^2*c^4 + 15*a*b^5 + 20*a*b^4*c - 19*a*b^3*c^2 - 21*a*b^2*c^3 + 20*a*b*c^4 + 17*a*c^5 + 17*b^5*c + 12*b^4*c^2 - 12*b^3*c^3 + 8*b^2*c^4 + 15*b*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / (a + b) + b / (b + c) + c / (c + a) + (9 * (a ^ 3 + b ^ 3 + c ^ 3)) / (a + b + c) ^ 3) ≥ 5 / 2) := @solution
#print axioms solution
