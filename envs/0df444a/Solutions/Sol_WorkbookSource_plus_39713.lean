-- Prove2me | solution 1 for WorkbookSource.plus_39713
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:38.218703+00:00
-- url     : https://prove2.me/submissions/dd7198d5-0510-48c9-b490-2d82fc66f1b2

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) : (x * y ^ 2 + z ^ 2 * y + z * x ^ 2) ^ 2 + (x ^ 2 * y + y ^ 2 * z + x * z ^ 2) ^ 2 + 6 * (x * y + z * x + y * z) * (x + y + z) * x * y * z ≥ 0   := by
  have h0 : 0 ≤ (18 : ℝ) * (x^2*y/6 + x^2*z/6 + x*y^2/6 + x*y*z + x*z^2/6 + y^2*z/6 + y*z^2/6)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (1/2 : ℝ) * (-x^2*y + x^2*z + x*y^2 - x*z^2 - y^2*z + y*z^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1]
example : (∀ (x y z : ℝ), (x * y ^ 2 + z ^ 2 * y + z * x ^ 2) ^ 2 + (x ^ 2 * y + y ^ 2 * z + x * z ^ 2) ^ 2 + 6 * (x * y + z * x + y * z) * (x + y + z) * x * y * z ≥ 0) := @solution
#print axioms solution
