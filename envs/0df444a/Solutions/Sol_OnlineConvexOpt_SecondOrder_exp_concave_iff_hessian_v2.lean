-- Prove2me | solution 1 for OnlineConvexOpt.SecondOrder.exp_concave_iff_hessian_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:35:18.963932+00:00
-- url     : https://prove2.me/submissions/8b7d9004-db2b-434e-b847-8386ffbfe87d

import Mathlib
import Definitions.Def_OnlineConvexOpt_SecondOrder_ExpConcave

open OnlineConvexOpt.SecondOrder


namespace OnlineConvexOpt.SecondOrder

theorem hess_core {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (α : ℝ) (hα : 0 < α) (f : E → ℝ) (x : E)
    (hf : ContDiffAt ℝ 2 f x) :
    IsExpConcaveAt α f x ↔
      ∀ v : E, α * ((fderiv ℝ f x) v) ^ 2 ≤ (fderiv ℝ (fderiv ℝ f) x) v v := by
  have hev : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 f y := hf.eventually (by simp)
  have hloc : (fderiv ℝ (fun y => Real.exp (-α * f y))) =ᶠ[nhds x]
      (fun y => (-α * Real.exp (-α * f y)) • fderiv ℝ f y) := by
    filter_upwards [hev] with y hy
    have hd : DifferentiableAt ℝ f y := hy.differentiableAt (by norm_num)
    have := ((hd.hasFDerivAt.const_mul (-α)).exp)
    rw [this.fderiv]
    ext v
    simp [smul_eq_mul]
    ring
  have hfx : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hL : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : HasFDerivAt (fun y => -α * Real.exp (-α * f y))
      (-α • (Real.exp (-α * f x) • (-α • fderiv ℝ f x))) x :=
    ((hfx.hasFDerivAt.const_mul (-α)).exp).const_mul (-α)
  have hD := hc.smul hL.hasFDerivAt
  unfold IsExpConcaveAt
  rw [hloc.fderiv_eq, show (fun y => (-α * Real.exp (-α * f y)) • fderiv ℝ f y) =
    ((fun y => -α * Real.exp (-α * f y)) • fderiv ℝ f) from rfl, hD.fderiv]
  have key : ∀ v : E, (((fun y => -α * Real.exp (-α * f y)) x •
      fderiv ℝ (fderiv ℝ f) x +
      (-α • (Real.exp (-α * f x) • (-α • fderiv ℝ f x))).smulRight (fderiv ℝ f x)) v v)
      = Real.exp (-α * f x) * α * (α * ((fderiv ℝ f x) v) ^ 2 - (fderiv ℝ (fderiv ℝ f) x) v v) := by
    intro v
    simp [smul_eq_mul]
    ring
  have hpos : 0 < Real.exp (-α * f x) * α := mul_pos (Real.exp_pos _) hα
  constructor
  · intro h v
    have := h v
    rw [key] at this
    have := nonpos_of_mul_nonpos_right this hpos
    linarith
  · intro h v
    rw [key]
    exact mul_nonpos_of_nonneg_of_nonpos hpos.le (by linarith [h v])

end OnlineConvexOpt.SecondOrder

open OnlineConvexOpt.SecondOrder
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem solution (α : ℝ) (hα : 0 < α) (f : E → ℝ) (x : E)
    (hf : ContDiffAt ℝ 2 f x) :
    IsExpConcaveAt α f x ↔
      ∀ v : E, α * ((fderiv ℝ f x) v) ^ 2 ≤ (fderiv ℝ (fderiv ℝ f) x) v v := by
  exact hess_core α hα f x hf
