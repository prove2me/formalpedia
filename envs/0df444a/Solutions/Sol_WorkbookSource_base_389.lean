-- Prove2me | solution 1 for WorkbookSource.base_389
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:40:48.200542+00:00
-- url     : https://prove2.me/submissions/f996d4ed-f07a-4047-bc91-5f21f4aa1ad5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y : ℝ) : 8 * (x ^ 4 + x ^ 3 * y + x * y ^ 3 + y ^ 4) ≤ 9 * (x ^ 4 + 2 * x ^ 2 * y ^ 2 + y ^ 4)  := by
  have h0 : 0 ≤ (16 : ℝ) * (-x^2/4 + x*y - y^2/4)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0]
example : (∀ (x y : ℝ), 8 * (x ^ 4 + x ^ 3 * y + x * y ^ 3 + y ^ 4) ≤ 9 * (x ^ 4 + 2 * x ^ 2 * y ^ 2 + y ^ 4)) := @solution
#print axioms solution
