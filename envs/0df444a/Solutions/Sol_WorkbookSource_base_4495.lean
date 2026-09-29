-- Prove2me | solution 1 for WorkbookSource.base_4495
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:40:55.756758+00:00
-- url     : https://prove2.me/submissions/61298b3f-fa6d-4f40-81b4-e06bd9339a05

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y : ℝ) : x^4 + 5 + y^2 + y^4 ≥ x^2 + 4*y + 2*x*y^2  := by
  have h0 : 0 ≤ (5 : ℝ) * (-x^2/5 - 2*y/5 + 1)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (1 : ℝ) * (-x + y^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (4/5 : ℝ) * (x^2 - y/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (x y : ℝ), x^4 + 5 + y^2 + y^4 ≥ x^2 + 4*y + 2*x*y^2) := @solution
#print axioms solution
