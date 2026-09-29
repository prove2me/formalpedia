-- Prove2me | solution 1 for WorkbookSource.base_52673
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:21:18.800029+00:00
-- url     : https://prove2.me/submissions/3779fe52-471e-489e-9e16-f2c87b43af4b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) : (y - z) ^ 4 + (z - x) ^ 4 + (x - y) ^ 4 + (9 / 2) * y * z * (y - z) ^ 2 ≥ 0  := by
  have h0 : 0 ≤ (5 : ℝ) * (-2*x^2/5 - x*y/5 + x*z + y^2/5 - y*z/5 - 2*z^2/5)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (24/5 : ℝ) * (-x^2/2 + x*y - 3*y^2/8 - y*z/4 + z^2/8)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (9/8 : ℝ) * (-y^2 + z^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (x y z : ℝ), (y - z) ^ 4 + (z - x) ^ 4 + (x - y) ^ 4 + (9 / 2) * y * z * (y - z) ^ 2 ≥ 0) := @solution
#print axioms solution
