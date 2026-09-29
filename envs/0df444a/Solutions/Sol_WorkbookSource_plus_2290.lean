-- Prove2me | solution 1 for WorkbookSource.plus_2290
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:19:04.539501+00:00
-- url     : https://prove2.me/submissions/5757eae2-66e6-49d1-9481-17c0b33e71dc

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 5 * (a * b + b * c + c * a)^3 + 27 * (a * b * c)^2 ≥ 18 * a * b * c * (a + b + c) * (a * b + b * c + c * a)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (5*a^3*b^3 - 3*a^3*b^2*c - 3*a^3*b*c^2 + 5*a^3*c^3 - 3*a^2*b^3*c + 3*a^2*b^2*c^2 - 3*a^2*b*c^3 - 3*a*b^3*c^2 - 3*a*b^2*c^3 + 5*b^3*c^3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (9 : ℝ) * a^4 * (b - a)^2 + (9 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (9 : ℝ) * a^4 * (c - b)^2 + (32 : ℝ) * a^3 * (b - a)^3 + (48 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (24 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (4 : ℝ) * a^3 * (c - b)^3 + (42 : ℝ) * a^2 * (b - a)^4 + (84 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (48 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (6 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (24 : ℝ) * a^1 * (b - a)^5 + (60 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (48 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (12 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (5 : ℝ) * (b - a)^6 + (15 : ℝ) * (b - a)^5 * (c - b)^1 + (15 : ℝ) * (b - a)^4 * (c - b)^2 + (5 : ℝ) * (b - a)^3 * (c - b)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (5*a^3*b^3 - 3*a^3*b^2*c - 3*a^3*b*c^2 + 5*a^3*c^3 - 3*a^2*b^3*c + 3*a^2*b^2*c^2 - 3*a^2*b*c^3 - 3*a*b^3*c^2 - 3*a*b^2*c^3 + 5*b^3*c^3) := by
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
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 5 * (a * b + b * c + c * a)^3 + 27 * (a * b * c)^2 ≥ 18 * a * b * c * (a + b + c) * (a * b + b * c + c * a)) := @solution
#print axioms solution
