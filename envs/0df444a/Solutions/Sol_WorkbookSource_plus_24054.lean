-- Prove2me | solution 1 for WorkbookSource.plus_24054
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:45:05.258139+00:00
-- url     : https://prove2.me/submissions/a5b42b6a-63a0-4346-826f-b6ad16b117f7

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 - b * c) / (b + c + 2 * a) + (b^2 - c * a) / (a + c + 2 * b) + (c^2 - a * b) / (a + b + 2 * c) ≥ 0   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4 + a^3*b + a^3*c - a^2*b^2 - 2*a^2*b*c - a^2*c^2 + a*b^3 - 2*a*b^2*c - 2*a*b*c^2 + a*c^3 + b^4 + b^3*c - b^2*c^2 + b*c^3 + c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^2 * (b - a)^2 + (8 : ℝ) * a^2 * (b - a)^1 * (c - b)^1 + (8 : ℝ) * a^2 * (c - b)^2 + (10 : ℝ) * a^1 * (b - a)^3 + (15 : ℝ) * a^1 * (b - a)^2 * (c - b)^1 + (17 : ℝ) * a^1 * (b - a)^1 * (c - b)^2 + (6 : ℝ) * a^1 * (c - b)^3 + (3 : ℝ) * (b - a)^4 + (6 : ℝ) * (b - a)^3 * (c - b)^1 + (8 : ℝ) * (b - a)^2 * (c - b)^2 + (5 : ℝ) * (b - a)^1 * (c - b)^3 + (1 : ℝ) * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4 + a^3*b + a^3*c - a^2*b^2 - 2*a^2*b*c - a^2*c^2 + a*b^3 - 2*a*b^2*c - 2*a*b*c^2 + a*c^3 + b^4 + b^3*c - b^2*c^2 + b*c^3 + c^4) := by
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
  have hn : 0 ≤ (a^4 + a^3*b + a^3*c - a^2*b^2 - 2*a^2*b*c - a^2*c^2 + a*b^3 - 2*a*b^2*c - 2*a*b*c^2 + a*c^3 + b^4 + b^3*c - b^2*c^2 + b*c^3 + c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 - b * c) / (b + c + 2 * a) + (b^2 - c * a) / (a + c + 2 * b) + (c^2 - a * b) / (a + b + 2 * c) ≥ 0) := @solution
#print axioms solution
