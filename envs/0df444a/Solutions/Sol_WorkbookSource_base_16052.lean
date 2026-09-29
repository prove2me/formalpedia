-- Prove2me | solution 1 for WorkbookSource.base_16052
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:52:08.83383+00:00
-- url     : https://prove2.me/submissions/31200031-6742-428a-9999-4e522cc92ef5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + b^3 + c^3) * (b * c + c * a + a * b) ≥ 3 * a * b * c * (a^2 + b^2 + c^2)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b + a^4*c - 2*a^3*b*c + a*b^4 - 2*a*b^3*c - 2*a*b*c^3 + a*c^4 + b^4*c + b*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (6 : ℝ) * a^3 * (b - a)^2 + (6 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (6 : ℝ) * a^3 * (c - b)^2 + (12 : ℝ) * a^2 * (b - a)^3 + (18 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (18 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (6 : ℝ) * a^2 * (c - b)^3 + (8 : ℝ) * a^1 * (b - a)^4 + (16 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (18 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (10 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (2 : ℝ) * a^1 * (c - b)^4 + (2 : ℝ) * (b - a)^5 + (5 : ℝ) * (b - a)^4 * (c - b)^1 + (6 : ℝ) * (b - a)^3 * (c - b)^2 + (4 : ℝ) * (b - a)^2 * (c - b)^3 + (1 : ℝ) * (b - a)^1 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b + a^4*c - 2*a^3*b*c + a*b^4 - 2*a*b^3*c - 2*a*b*c^3 + a*c^4 + b^4*c + b*c^4) := by
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
  nlinarith only [hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^3 + b^3 + c^3) * (b * c + c * a + a * b) ≥ 3 * a * b * c * (a^2 + b^2 + c^2)) := @solution
#print axioms solution
