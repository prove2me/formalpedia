-- Prove2me | solution 1 for WorkbookSource.base_8651
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:41:03.776404+00:00
-- url     : https://prove2.me/submissions/21d13b3a-1b36-4d16-a605-baa03ea66883

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z: ℝ) :  (x^2 + y^2 + z^2)^3 ≥ 8 * (x^3 * y^3 + y^3 * z^3 + x^3 * z^3) + 3 * x^2 * y^2 * z^2 + 3 * (x-y)^2 * (x-z)^2 * (y-z)^2  := by
  have h0 : 0 ≤ (6 : ℝ) * (x^3/3 - x^2*y/3 - x^2*z/3 - x*y^2/3 + x*y*z - x*z^2/3 + y^3/3 - y^2*z/3 - y*z^2/3 + z^3/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (7/3 : ℝ) * (x^3/14 + 11*x^2*y/14 - x^2*z/2 - x*y^2/2 + x*z^2/7 - 5*y^3/14 - 13*y^2*z/14 + y*z^2 + 2*z^3/7)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (16/7 : ℝ) * (-3*x^3/8 - 5*x^2*y/8 - 7*x^2*z/8 + 7*x*y^2/8 + x*z^2 + y^3/8 - 3*y^2*z/8 + z^3/4)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (x y z: ℝ), (x^2 + y^2 + z^2)^3 ≥ 8 * (x^3 * y^3 + y^3 * z^3 + x^3 * z^3) + 3 * x^2 * y^2 * z^2 + 3 * (x-y)^2 * (x-z)^2 * (y-z)^2) := @solution
#print axioms solution
