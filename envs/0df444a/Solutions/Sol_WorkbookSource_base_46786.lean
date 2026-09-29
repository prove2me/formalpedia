-- Prove2me | solution 1 for WorkbookSource.base_46786
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:21:16.100743+00:00
-- url     : https://prove2.me/submissions/ea482145-1dc7-4411-bd00-b11361ba67ef

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution  (a b c d : ℝ) :
  3 / 4 * (a * c + b * d)^2 ≤ (a^2 - a * b + b^2) * (c^2 + c * d + d^2)  := by
  have h0 : 0 ≤ (1 : ℝ) * (-a*c/2 - a*d + b*c + b*d/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0]
example : (∀ (a b c d : ℝ), 3 / 4 * (a * c + b * d)^2 ≤ (a^2 - a * b + b^2) * (c^2 + c * d + d^2)) := @solution
#print axioms solution
