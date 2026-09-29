-- Prove2me | solution 1 for WorkbookSource.base_33481
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:11.044092+00:00
-- url     : https://prove2.me/submissions/9a38054c-7bb4-4049-a264-131cd1833476

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y : ℝ) : (x^2 + y^2)^2 + x^3 + y^3 + 4*x*y^2 + x^2 + y^2 ≥ 3*x^3*y + 5*x^2*y + x*y  := by
  have h0 : 0 ≤ (3 : ℝ) * (-x^2/2 + x*y - x/2 + y/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (1 : ℝ) * (-x^2/2 + x/2 + y^2 + y/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1]
example : (∀ (x y : ℝ), (x^2 + y^2)^2 + x^3 + y^3 + 4*x*y^2 + x^2 + y^2 ≥ 3*x^3*y + 5*x^2*y + x*y) := @solution
#print axioms solution
