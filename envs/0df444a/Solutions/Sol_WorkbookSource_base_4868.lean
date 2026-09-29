-- Prove2me | solution 1 for WorkbookSource.base_4868
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:40:56.52392+00:00
-- url     : https://prove2.me/submissions/e7c738f5-78f1-4192-91d8-7c0bd44fc780

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) : x ^ 4 + y ^ 4 + z ^ 4 + 2 * x * y * z * (x + y + z) ≥ x ^ 3 * y + y ^ 3 * z + z ^ 3 * x  := by
  have h0 : 0 ≤ (1 : ℝ) * (-x^2/2 + x*y/2 - x*z/2 - y^2/2 + z^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (1 : ℝ) * (x^2/2 + x*y/2 + x*z/2 - y^2/2 + y*z)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (1/2 : ℝ) * (-x^2 + x*y + x*z + y^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (x y z : ℝ), x ^ 4 + y ^ 4 + z ^ 4 + 2 * x * y * z * (x + y + z) ≥ x ^ 3 * y + y ^ 3 * z + z ^ 3 * x) := @solution
#print axioms solution
