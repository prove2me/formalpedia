-- Prove2me | solution 1 for WorkbookSource.base_32699
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:09.645209+00:00
-- url     : https://prove2.me/submissions/06722cbb-c6c0-4b2f-ae4e-371bfc6b8bb1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) : 3 * (x ^ 2 - x + 1) * (y ^ 2 - y + 1) * (z ^ 2 - z + 1) ≥ (x*y*z) ^ 2 + x*y*z + 1  := by
  have h0 : 0 ≤ (3 : ℝ) * (x*y*z/3 - x*y/6 - x*z/2 + x/6 - y*z/2 + y/6 + z - 1/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (35/12 : ℝ) * (2*x*y*z/7 - 17*x*y/35 - 3*x*z/35 + x/7 - 3*y*z/7 + y - 3/7)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (20/7 : ℝ) * (x*y*z/4 - 17*x*y/40 - 17*x*z/40 + x - y*z/40 - 3/8)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (137/80 : ℝ) * (-50*x*y*z/137 - 31*x*y/137 - 31*x*z/137 + y*z - 25/137)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (1113/685 : ℝ) * (-25*x*y*z/53 - 31*x*y/106 + x*z - 25/106)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h5 : 0 ≤ (315/212 : ℝ) * (-2*x*y*z/3 + x*y - 1/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4, h5]
example : (∀ (x y z : ℝ), 3 * (x ^ 2 - x + 1) * (y ^ 2 - y + 1) * (z ^ 2 - z + 1) ≥ (x*y*z) ^ 2 + x*y*z + 1) := @solution
#print axioms solution
