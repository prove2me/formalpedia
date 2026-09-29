-- Prove2me | solution 1 for WorkbookSource.base_35375
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:13.104347+00:00
-- url     : https://prove2.me/submissions/2d555390-57b4-497b-9b01-da6159bf2357

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) : (2 * x ^ 2 + 1) * (2 * y ^ 2 + 1) * (2 * z ^ 2 + 1) ≥ 3 * (x * y + x * z + y * z) ^ 2  := by
  have h0 : 0 ≤ (8 : ℝ) * (x*y*z - x/3 - y/3 - z/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (10/9 : ℝ) * (-x/2 - y/2 + z)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (1 : ℝ) * (-x*y/3 - x*z/3 - y*z/3 + 1)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (8/9 : ℝ) * (-x*y/2 - x*z/2 + y*z)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (5/6 : ℝ) * (-x + y)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h5 : 0 ≤ (2/3 : ℝ) * (-x*y + x*z)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4, h5]
example : (∀ (x y z : ℝ), (2 * x ^ 2 + 1) * (2 * y ^ 2 + 1) * (2 * z ^ 2 + 1) ≥ 3 * (x * y + x * z + y * z) ^ 2) := @solution
#print axioms solution
