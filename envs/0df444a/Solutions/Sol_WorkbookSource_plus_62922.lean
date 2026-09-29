-- Prove2me | solution 1 for WorkbookSource.plus_62922
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:41.0797+00:00
-- url     : https://prove2.me/submissions/fe3be23f-d830-4413-bcdc-c0e255acec3a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) : (4 * x ^ 6 + x ^ 4 * y ^ 2 + x ^ 4 * z ^ 2 - 6 * x ^ 3 * y ^ 3) + (4 * y ^ 6 + y ^ 4 * z ^ 2 + y ^ 4 * x ^ 2 - 6 * y ^ 3 * z ^ 3) + (4 * z ^ 6 + z ^ 4 * x ^ 2 + z ^ 4 * y ^ 2 - 6 * z ^ 3 * x ^ 3) ≥ 0   := by
  have h0 : 0 ≤ (4 : ℝ) * (-x^3/2 - y^3/2 + z^3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (3 : ℝ) * (-x^3 + y^3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (1 : ℝ) * (-y^2*z + y*z^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (1 : ℝ) * (-x^2*z + x*z^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (1 : ℝ) * (-x^2*y + x*y^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4]
example : (∀ (x y z : ℝ), (4 * x ^ 6 + x ^ 4 * y ^ 2 + x ^ 4 * z ^ 2 - 6 * x ^ 3 * y ^ 3) + (4 * y ^ 6 + y ^ 4 * z ^ 2 + y ^ 4 * x ^ 2 - 6 * y ^ 3 * z ^ 3) + (4 * z ^ 6 + z ^ 4 * x ^ 2 + z ^ 4 * y ^ 2 - 6 * z ^ 3 * x ^ 3) ≥ 0) := @solution
#print axioms solution
