-- Prove2me | solution 1 for WorkbookSource.plus_14282
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:26:55.112633+00:00
-- url     : https://prove2.me/submissions/d8feea59-7fcf-42a4-8106-b86639125d51

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 1) : 216 * (a^2 * b^2 + a^2 * c^2 + b^2 * c^2) ≤ 11 * ((a - b)^2 + (a - c)^2 + (b - c)^2) + 8   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (30*a^4 + 54*a^3*b + 54*a^3*c - 168*a^2*b^2 + 30*a^2*b*c - 168*a^2*c^2 + 54*a*b^3 + 30*a*b^2*c + 30*a*b*c^2 + 54*a*c^3 + 30*b^4 + 54*b^3*c - 168*b^2*c^2 + 54*b*c^3 + 30*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (198 : ℝ) * a^2 * (b - a)^2 + (198 : ℝ) * a^2 * (b - a)^1 * (c - b)^1 + (198 : ℝ) * a^2 * (c - b)^2 + (168 : ℝ) * a^1 * (b - a)^3 + (252 : ℝ) * a^1 * (b - a)^2 * (c - b)^1 + (540 : ℝ) * a^1 * (b - a)^1 * (c - b)^2 + (228 : ℝ) * a^1 * (c - b)^3 + (174 : ℝ) * (b - a)^2 * (c - b)^2 + (174 : ℝ) * (b - a)^1 * (c - b)^3 + (30 : ℝ) * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (30*a^4 + 54*a^3*b + 54*a^3*c - 168*a^2*b^2 + 30*a^2*b*c - 168*a^2*c^2 + 54*a*b^3 + 30*a*b^2*c + 30*a*b*c^2 + 54*a*c^3 + 30*b^4 + 54*b^3*c - 168*b^2*c^2 + 54*b*c^3 + 30*c^4) := by
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
  have he : (-216*a^2*b^2 - 216*a^2*c^2 + 22*a^2 - 22*a*b - 22*a*c - 216*b^2*c^2 + 22*b^2 - 22*b*c + 22*c^2 + 8) = (30*a^4 + 54*a^3*b + 54*a^3*c - 168*a^2*b^2 + 30*a^2*b*c - 168*a^2*c^2 + 54*a*b^3 + 30*a*b^2*c + 30*a*b*c^2 + 54*a*c^3 + 30*b^4 + 54*b^3*c - 168*b^2*c^2 + 54*b*c^3 + 30*c^4) := by
    linear_combination (-30*a^3 - 24*a^2*b - 24*a^2*c - 30*a^2 - 24*a*b^2 + 18*a*b*c + 6*a*b - 24*a*c^2 + 6*a*c - 8*a - 30*b^3 - 24*b^2*c - 30*b^2 - 24*b*c^2 + 6*b*c - 8*b - 30*c^3 - 30*c^2 - 8*c - 8) * hab
  nlinarith only [hp, he]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 1), 216 * (a^2 * b^2 + a^2 * c^2 + b^2 * c^2) ≤ 11 * ((a - b)^2 + (a - c)^2 + (b - c)^2) + 8) := @solution
#print axioms solution
