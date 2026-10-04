-- Prove2me | solution 1 for RadialGeometry.radial_derivative_tangent_injective
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T19:19:01.518802+00:00
-- url     : https://prove2.me/submissions/2f755642-0e80-457b-b854-f8a1953c6514

import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic

set_option autoImplicit false

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : E → ℝ) (u v : E) (ha : DifferentiableAt ℝ a u)
    (hane : a u ≠ 0) (hv : inner ℝ u v = 0)
    (hz : fderiv ℝ (fun x => a x • x) u v = 0) : v = 0 := by
  have hd : fderiv ℝ (fun x => a x • x) u v =
      (fderiv ℝ a u v) • u + a u • v := by
    rw [fderiv_fun_smul ha
      (show DifferentiableAt ℝ (fun x : E => x) u from differentiableAt_id)]
    simp only [add_apply, ContinuousLinearMap.smulRight_apply,
      smul_apply, fderiv_fun_id, ContinuousLinearMap.id_apply]
    exact add_comm _ _
  have h : a u * inner ℝ v v = 0 := by
    have hp := congrArg (fun z : E => inner ℝ z v) (hd.symm.trans hz)
    simpa only [inner_add_left, real_inner_smul_left, hv, mul_zero,
      zero_add, inner_zero_left] using hp
  exact inner_self_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hane)
