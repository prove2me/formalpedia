-- Prove2me | solution 1 for WorkbookSource.base_7194
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:59.692505+00:00
-- url     : https://prove2.me/submissions/2ba5c0e0-3f77-4376-a280-ec677ace4af7

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) : x * (x + y) ^ 3 + y * (y + z) ^ 3 + z * (z + x) ^ 3 ≥ (8 / 27) * (x + y + z) ^ 4  := by
  have h0 : 0 ≤ (43/24 : ℝ) * (-205*x^2/387 - 179*x*y/387 - 179*x*z/387 + 196*y^2/387 + y*z - 20*z^2/387)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (14716/10449 : ℝ) * (-44435*x^2/117728 - 179*x*y/208 + x*z - 44251*y^2/117728 + 4517*z^2/7358)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (8207/22464 : ℝ) * (17*x^2/566 + x*y - 199*y^2/566 - 192*z^2/283)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (x y z : ℝ), x * (x + y) ^ 3 + y * (y + z) ^ 3 + z * (z + x) ^ 3 ≥ (8 / 27) * (x + y + z) ^ 4) := @solution
#print axioms solution
