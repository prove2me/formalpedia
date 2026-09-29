-- Prove2me | solution 1 for WorkbookSource.base_867
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:36:21.310509+00:00
-- url     : https://prove2.me/submissions/c76ddd52-1985-4f7e-a310-8f0564393e78

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y : ℝ) (hx: x ≥ 0) (hy: y ≥ 0) : 5 * (x^4 + y^4) ≥ (x^2 + y^2) * (x + y + |x - y|)^2  := by
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (by linarith : x-y ≤ 0)]
    nlinarith [sq_nonneg (y^2-2*x^2),sq_nonneg (x^2)]
  · rw [abs_of_nonneg (by linarith : 0 ≤ x-y)]
    nlinarith [sq_nonneg (x^2-2*y^2),sq_nonneg (y^2)]
example : (∀ (x y : ℝ) (hx: x ≥ 0) (hy: y ≥ 0), 5 * (x^4 + y^4) ≥ (x^2 + y^2) * (x + y + |x - y|)^2) := @solution
#print axioms solution
