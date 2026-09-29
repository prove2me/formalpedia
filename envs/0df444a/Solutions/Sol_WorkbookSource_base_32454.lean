-- Prove2me | solution 1 for WorkbookSource.base_32454
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:36:05.261202+00:00
-- url     : https://prove2.me/submissions/b0b6ff8d-7d9a-479b-aa1c-c43865e6457d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / ((2 * a + b) * (2 * a + c)) + 1 / ((2 * b + c) * (2 * b + a)) + 1 / ((2 * c + a) * (2 * c + b)) ≥ 1 / (a * b + b * c + c * a)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^4*b^2 + 4*a^4*b*c + 4*a^4*c^2 + 4*a^3*b^3 - a^3*b^2*c - a^3*b*c^2 + 4*a^3*c^3 + 4*a^2*b^4 - a^2*b^3*c - 42*a^2*b^2*c^2 - a^2*b*c^3 + 4*a^2*c^4 + 4*a*b^4*c - a*b^3*c^2 - a*b^2*c^3 + 4*a*b*c^4 + 4*b^4*c^2 + 4*b^3*c^3 + 4*b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (54 : ℝ) * a^4 * (b - a)^2 + (54 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (54 : ℝ) * a^4 * (c - b)^2 + (162 : ℝ) * a^3 * (b - a)^3 + (243 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (189 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (54 : ℝ) * a^3 * (c - b)^3 + (174 : ℝ) * a^2 * (b - a)^4 + (348 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (279 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (105 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (12 : ℝ) * a^2 * (c - b)^4 + (78 : ℝ) * a^1 * (b - a)^5 + (195 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (180 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (75 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (12 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (12 : ℝ) * (b - a)^6 + (36 : ℝ) * (b - a)^5 * (c - b)^1 + (40 : ℝ) * (b - a)^4 * (c - b)^2 + (20 : ℝ) * (b - a)^3 * (c - b)^3 + (4 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^4*b^2 + 4*a^4*b*c + 4*a^4*c^2 + 4*a^3*b^3 - a^3*b^2*c - a^3*b*c^2 + 4*a^3*c^3 + 4*a^2*b^4 - a^2*b^3*c - 42*a^2*b^2*c^2 - a^2*b*c^3 + 4*a^2*c^4 + 4*a*b^4*c - a*b^3*c^2 - a*b^2*c^3 + 4*a*b*c^4 + 4*b^4*c^2 + 4*b^3*c^3 + 4*b^2*c^4) := by
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
  have hn : 0 ≤ (4*a^4*b^2 + 4*a^4*b*c + 4*a^4*c^2 + 4*a^3*b^3 - a^3*b^2*c - a^3*b*c^2 + 4*a^3*c^3 + 4*a^2*b^4 - a^2*b^3*c - 42*a^2*b^2*c^2 - a^2*b*c^3 + 4*a^2*c^4 + 4*a*b^4*c - a*b^3*c^2 - a*b^2*c^3 + 4*a*b*c^4 + 4*b^4*c^2 + 4*b^3*c^3 + 4*b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 1 / ((2 * a + b) * (2 * a + c)) + 1 / ((2 * b + c) * (2 * b + a)) + 1 / ((2 * c + a) * (2 * c + b)) ≥ 1 / (a * b + b * c + c * a)) := @solution
#print axioms solution
