-- Prove2me | solution 1 for WorkbookSource.plus_36412
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:54:29.950002+00:00
-- url     : https://prove2.me/submissions/4467d5b2-81a0-43c8-a222-2a31bccf3e0d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (2 * a + b + c) + b^2 / (a + 2 * b + c) + c^2 / (a + b + 2 * c)) ≥ (a + b + c) / 4   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^4 + 3*a^3*b + 3*a^3*c + 2*a^2*b^2 - 10*a^2*b*c + 2*a^2*c^2 + 3*a*b^3 - 10*a*b^2*c - 10*a*b*c^2 + 3*a*c^3 + 2*b^4 + 3*b^3*c + 2*b^2*c^2 + 3*b*c^3 + 2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (24 : ℝ) * a^2 * (b - a)^2 + (24 : ℝ) * a^2 * (b - a)^1 * (c - b)^1 + (24 : ℝ) * a^2 * (c - b)^2 + (34 : ℝ) * a^1 * (b - a)^3 + (51 : ℝ) * a^1 * (b - a)^2 * (c - b)^1 + (45 : ℝ) * a^1 * (b - a)^1 * (c - b)^2 + (14 : ℝ) * a^1 * (c - b)^3 + (12 : ℝ) * (b - a)^4 + (24 : ℝ) * (b - a)^3 * (c - b)^1 + (23 : ℝ) * (b - a)^2 * (c - b)^2 + (11 : ℝ) * (b - a)^1 * (c - b)^3 + (2 : ℝ) * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^4 + 3*a^3*b + 3*a^3*c + 2*a^2*b^2 - 10*a^2*b*c + 2*a^2*c^2 + 3*a*b^3 - 10*a*b^2*c - 10*a*b*c^2 + 3*a*c^3 + 2*b^4 + 3*b^3*c + 2*b^2*c^2 + 3*b*c^3 + 2*c^4) := by
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
  have hn : 0 ≤ ((a + b + c)*(2*a^3 + a^2*b + a^2*c + a*b^2 - 12*a*b*c + a*c^2 + 2*b^3 + b^2*c + b*c^2 + 2*c^3)) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 / (2 * a + b + c) + b^2 / (a + 2 * b + c) + c^2 / (a + b + 2 * c)) ≥ (a + b + c) / 4) := @solution
#print axioms solution
