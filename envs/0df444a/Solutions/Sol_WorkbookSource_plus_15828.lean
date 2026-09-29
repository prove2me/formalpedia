-- Prove2me | solution 1 for WorkbookSource.plus_15828
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T13:12:53.272829+00:00
-- url     : https://prove2.me/submissions/d64d333a-a8a1-45a4-87be-798496f39a85

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution : ¬ (∃ x : ℝ, x^6+x^5+x^4-x^3-x^2+1 = 0) := by
  rintro ⟨x,hx⟩
  have hid : x^6+x^5+x^4-x^3-x^2+1 = (-x^3/2-11*x^2/8+1)^2 + (7/4 : ℝ)*(-2*x^3/7+x)^2 + (7/64 : ℝ)*(-12*x^3/7+x^2)^2 + (2/7 : ℝ)*(x^3)^2 := by ring
  have hz : (x^3)^2 = 0 := by
    nlinarith only [hx,hid,sq_nonneg (-x^3/2-11*x^2/8+1),sq_nonneg (-2*x^3/7+x),sq_nonneg (-12*x^3/7+x^2),sq_nonneg (x^3)]
  have h3 : x^3=0 := sq_eq_zero_iff.mp hz
  have h0 : x=0 := (pow_eq_zero_iff (by decide : (3:ℕ) ≠ 0)).mp h3
  subst x
  norm_num at hx
example : (¬ (∃ x : ℝ, x^6+x^5+x^4-x^3-x^2+1 = 0)) := @solution
#print axioms solution
