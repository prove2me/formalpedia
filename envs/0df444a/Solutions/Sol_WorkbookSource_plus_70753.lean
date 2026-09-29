-- Prove2me | solution 1 for WorkbookSource.plus_70753
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:45:26.638019+00:00
-- url     : https://prove2.me/submissions/043c25f1-769b-4019-9ae5-5e7c3f2956ee

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 2) : (a^2 + b * c) * (b^2 + c * a) + (b^2 + c * a) * (c^2 + a * b) + (c^2 + a * b) * (a^2 + b * c) ≤ 3   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (3*a^4/16 - a^3*b/4 - a^3*c/4 + a^2*b^2/8 + 5*a^2*b*c/4 + a^2*c^2/8 - a*b^3/4 + 5*a*b^2*c/4 + 5*a*b*c^2/4 - a*c^3/4 + 3*b^4/16 - b^3*c/4 + b^2*c^2/8 - b*c^3/4 + 3*c^4/16) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (51/16 : ℝ) * a^4 + (17/2 : ℝ) * a^3 * (b - a)^1 + (17/4 : ℝ) * a^3 * (c - b)^1 + (15/2 : ℝ) * a^2 * (b - a)^2 + (15/2 : ℝ) * a^2 * (b - a)^1 * (c - b)^1 + (9/8 : ℝ) * a^2 * (c - b)^2 + (2 : ℝ) * a^1 * (b - a)^3 + (3 : ℝ) * a^1 * (b - a)^2 * (c - b)^1 + (3/2 : ℝ) * a^1 * (b - a)^1 * (c - b)^2 + (1/4 : ℝ) * a^1 * (c - b)^3 + (1/2 : ℝ) * (b - a)^2 * (c - b)^2 + (1/2 : ℝ) * (b - a)^1 * (c - b)^3 + (3/16 : ℝ) * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*a^4/16 - a^3*b/4 - a^3*c/4 + a^2*b^2/8 + 5*a^2*b*c/4 + a^2*c^2/8 - a*b^3/4 + 5*a*b^2*c/4 + 5*a*b*c^2/4 - a*c^3/4 + 3*b^4/16 - b^3*c/4 + b^2*c^2/8 - b*c^3/4 + 3*c^4/16) := by
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
  have he : (-a^3*b - a^3*c - a^2*b^2 - a^2*b*c - a^2*c^2 - a*b^3 - a*b^2*c - a*b*c^2 - a*c^3 - b^3*c - b^2*c^2 - b*c^3 + 3) = (3*a^4/16 - a^3*b/4 - a^3*c/4 + a^2*b^2/8 + 5*a^2*b*c/4 + a^2*c^2/8 - a*b^3/4 + 5*a*b^2*c/4 + 5*a*b*c^2/4 - a*c^3/4 + 3*b^4/16 - b^3*c/4 + b^2*c^2/8 - b*c^3/4 + 3*c^4/16) := by
    linear_combination (-3*a^3/16 - 9*a^2*b/16 - 9*a^2*c/16 - 3*a^2/8 - 9*a*b^2/16 - 9*a*b*c/8 - 3*a*b/4 - 9*a*c^2/16 - 3*a*c/4 - 3*a/4 - 3*b^3/16 - 9*b^2*c/16 - 3*b^2/8 - 9*b*c^2/16 - 3*b*c/4 - 3*b/4 - 3*c^3/16 - 3*c^2/8 - 3*c/4 - 3/2) * hab
  nlinarith only [hp, he]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 2), (a^2 + b * c) * (b^2 + c * a) + (b^2 + c * a) * (c^2 + a * b) + (c^2 + a * b) * (a^2 + b * c) ≤ 3) := @solution
#print axioms solution
