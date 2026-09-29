-- Prove2me | solution 1 for OnlineConvexOpt.SecondOrder.exp_concave_iff_hessian
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:53:38.8815+00:00
-- url     : https://prove2.me/submissions/69126a05-1fd7-48c4-9e65-ae651f69c12e

import Mathlib
import Definitions.Def_OnlineConvexOpt_SecondOrder_ExpConcave

open OnlineConvexOpt.SecondOrder


namespace OnlineConvexOpt.SecondOrder

theorem hess_counter : ¬ (∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (α : ℝ) (f : E → ℝ) (x : E) (hf : ContDiffAt ℝ 2 f x),
    IsExpConcaveAt α f x ↔
      ∀ v : E, α * ((fderiv ℝ f x) v) ^ 2 ≤ (fderiv ℝ (fderiv ℝ f) x) v v) := by
  intro H
  let L : ℝ →L[ℝ] ℝ := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-2 : ℝ)
  have h1 : ∀ y : ℝ, HasFDerivAt (fun y : ℝ => -(y * y)) (y • L) y := by
    intro y
    have hd : HasDerivAt (fun y : ℝ => -(y * y)) (-(2 * y)) y :=
      ((hasDerivAt_id' y).mul (hasDerivAt_id' y)).neg.congr_deriv (by ring)
    refine hd.hasFDerivAt.congr_fderiv ?_
    ext; simp [L]; ring
  have h2 : fderiv ℝ (fun y : ℝ => -(y * y)) = fun y => y • L := by
    funext y; exact (h1 y).fderiv
  have h3 : HasFDerivAt (fun y : ℝ => y • L) ((ContinuousLinearMap.id ℝ ℝ).smulRight L) 0 :=
    (hasFDerivAt_id (0:ℝ)).smul_const L
  have hc : ContDiffAt ℝ 2 (fun y : ℝ => -(y * y)) 0 := by fun_prop
  have h := (H (0:ℝ) (fun y : ℝ => -(y * y)) 0 hc).mp (by
    intro v
    simp only [zero_mul, Real.exp_zero, neg_zero]
    simp)
  have := h 1
  rw [h2, h3.fderiv] at this
  simp [L] at this
  norm_num at this

end OnlineConvexOpt.SecondOrder

open OnlineConvexOpt.SecondOrder


theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (α : ℝ) (f : E → ℝ) (x : E) (hf : ContDiffAt ℝ 2 f x),
    IsExpConcaveAt α f x ↔
      ∀ v : E, α * ((fderiv ℝ f x) v) ^ 2 ≤ (fderiv ℝ (fderiv ℝ f) x) v v) := OnlineConvexOpt.SecondOrder.hess_counter
