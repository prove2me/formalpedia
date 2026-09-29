-- Prove2me | solution 1 for WorkbookSource.plus_22071
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:35.687511+00:00
-- url     : https://prove2.me/submissions/0017ac8a-75f8-4edb-85ed-1b88cf8bd7f6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) : 8 * (x ^ 2 + x * y + y ^ 2) * (y ^ 2 + y * z + z ^ 2) * (z ^ 2 + z * x + x ^ 2) ≥ 27 * (x + y) * (y + z) * (z + x) * x * y * z   := by
  have h0 : 0 ≤ (12 : ℝ) * (-x^2*y/6 - x^2*z/6 - x*y^2/6 + x*y*z - x*z^2/6 - y^2*z/6 - y*z^2/6)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (23/3 : ℝ) * (-22*x^2*y/23 - x^2*z/2 - x*y^2/2 + 11*x*z^2/23 + 11*y^2*z/23 + y*z^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (136/23 : ℝ) * (-15*x^2*y/272 - 253*x^2*z/272 + 253*x*y^2/272 - 257*x*z^2/272 + y^2*z)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (345/544 : ℝ) * (-x^2*y + 11*x^2*z/23 - 11*x*y^2/23 + x*z^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (45/92 : ℝ) * (-x^2*z + x*y^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4]
example : (∀ (x y z : ℝ), 8 * (x ^ 2 + x * y + y ^ 2) * (y ^ 2 + y * z + z ^ 2) * (z ^ 2 + z * x + x ^ 2) ≥ 27 * (x + y) * (y + z) * (z + x) * x * y * z) := @solution
#print axioms solution
