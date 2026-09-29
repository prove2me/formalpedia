-- Prove2me | solution 1 for WorkbookSource.plus_39085
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:36.353578+00:00
-- url     : https://prove2.me/submissions/60bcc5c5-77af-4af5-ab2b-645b5f9f1016

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : 3 * (a ^ 4 + b ^ 4 + c ^ 4) + 4 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) - 6 * a * b * c * (a + b + c) ≥ 0   := by
  have h0 : 0 ≤ (3 : ℝ) * (-a^2/3 - 2*a*b/3 + 2*a*c/3 - b^2/3 + c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (8/3 : ℝ) * (-a^2/2 - a*b/4 - a*c/2 + b^2 + 3*b*c/4)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (2 : ℝ) * (a^2 + a*b/2 - b*c/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (a b c : ℝ), 3 * (a ^ 4 + b ^ 4 + c ^ 4) + 4 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) - 6 * a * b * c * (a + b + c) ≥ 0) := @solution
#print axioms solution
