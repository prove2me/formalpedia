-- Prove2me | solution 1 for WorkbookSource.base_19226
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:44:42.023767+00:00
-- url     : https://prove2.me/submissions/f2b7686c-94c3-4373-8e6e-9c4b486cd73f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution  (x y z : ℝ) :
  (x^2 + 1) * (y^2 + 1) * (z^2 + 1) + 4 * x * y * z * (x + y + z) ≥ 0  := by
  have h0 : 0 ≤ (1 : ℝ) * (-x*y - x*z - y*z + 1)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (1 : ℝ) * (x*y*z + x + y + z)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1]
example : (∀ (x y z : ℝ), (x^2 + 1) * (y^2 + 1) * (z^2 + 1) + 4 * x * y * z * (x + y + z) ≥ 0) := @solution
#print axioms solution
