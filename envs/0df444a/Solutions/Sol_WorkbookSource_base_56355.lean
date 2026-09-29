-- Prove2me | solution 1 for WorkbookSource.base_56355
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:21:19.534133+00:00
-- url     : https://prove2.me/submissions/6b919915-3550-4570-82db-5d94fd6e2141

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) : (x ^ 3 + y ^ 3 + z ^ 3) ^ 2 + 3 * (x * y * z) ^ 2 ≥ 4 * (y ^ 3 * z ^ 3 + z ^ 3 * x ^ 3 + x ^ 3 * y ^ 3) + 4 / 5 * (x - y) ^ 2 * (y - z) ^ 2 * (z - x) ^ 2  := by
  have h0 : 0 ≤ (12/5 : ℝ) * (x^3/3 - x^2*y/3 - x^2*z/3 - x*y^2/3 + x*y*z - x*z^2/3 + y^3/3 - y^2*z/3 - y*z^2/3 + z^3/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (11/15 : ℝ) * (-x^3/2 + x^2*y/2 - 19*x^2*z/22 + x*y^2/2 + 4*x*z^2/11 - y^3/2 - 19*y^2*z/22 + 4*y*z^2/11 + z^3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (7/11 : ℝ) * (11*x^3/14 + 11*x^2*y/14 - 3*x^2*z/14 - 11*x*y^2/14 - 4*x*z^2/7 - 11*y^3/14 - 3*y^2*z/14 + y*z^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (3/7 : ℝ) * (-x^3/2 - x^2*y/2 - x^2*z/2 + x*y^2/2 + x*z^2 + y^3/2 - y^2*z/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (1/20 : ℝ) * (x^3 - x^2*y - x^2*z + x*y^2 - y^3 + y^2*z)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4]
example : (∀ (x y z : ℝ), (x ^ 3 + y ^ 3 + z ^ 3) ^ 2 + 3 * (x * y * z) ^ 2 ≥ 4 * (y ^ 3 * z ^ 3 + z ^ 3 * x ^ 3 + x ^ 3 * y ^ 3) + 4 / 5 * (x - y) ^ 2 * (y - z) ^ 2 * (z - x) ^ 2) := @solution
#print axioms solution
