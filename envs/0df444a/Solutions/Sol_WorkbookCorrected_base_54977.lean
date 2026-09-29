-- Prove2me | solution 1 for WorkbookCorrected.base_54977
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T12:12:55.730309+00:00
-- url     : https://prove2.me/submissions/f4d9b3c4-0d20-487b-80f4-7d883569ef51

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution : (∀ (x y z : ℝ) (h : x + y*z = 1), 2*x^2 + 3*y^2 + 4*z^2 ≥ 2) ∧ ((1 : ℝ) + 0*0 = 1 ∧ 2*(1 : ℝ)^2 + 3*0^2 + 4*0^2 = 2) := by
  constructor
  · intro x y z h
    have hx : x = 1-y*z := by linarith only [h]
    rw [hx]
    nlinarith only [sq_nonneg (y*z), sq_nonneg (3*y-2*z), sq_nonneg z]
  · norm_num
example : ((∀ (x y z : ℝ) (h : x + y*z = 1), 2*x^2 + 3*y^2 + 4*z^2 ≥ 2) ∧ ((1 : ℝ) + 0*0 = 1 ∧ 2*(1 : ℝ)^2 + 3*0^2 + 4*0^2 = 2)) := @solution
#print axioms solution
