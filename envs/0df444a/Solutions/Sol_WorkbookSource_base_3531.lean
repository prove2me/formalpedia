-- Prove2me | solution 1 for WorkbookSource.base_3531
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:40:52.560366+00:00
-- url     : https://prove2.me/submissions/7c38e531-91bd-4c98-8b9e-763b2f4d38a6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y : ℝ) : (x^2 * (2 * x^2 - 2 * x + 1) + 1) * (y^2 * (2 * y^2 - 2 * y + 1) + 1) ≥ (2 * x^2 * y^2 - x * y * (x + y) + 1)^2  := by
  have h0 : 0 ≤ (2 : ℝ) * (-x^2 + x/2 + y^2 - y/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (1 : ℝ) * (-x^2*y - x*y^2 + x*y)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (1/2 : ℝ) * (x + y)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (x y : ℝ), (x^2 * (2 * x^2 - 2 * x + 1) + 1) * (y^2 * (2 * y^2 - 2 * y + 1) + 1) ≥ (2 * x^2 * y^2 - x * y * (x + y) + 1)^2) := @solution
#print axioms solution
