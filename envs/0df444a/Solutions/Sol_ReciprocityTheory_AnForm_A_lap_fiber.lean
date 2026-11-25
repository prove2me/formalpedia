-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.lap_fiber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:06:17.786791+00:00
-- url     : https://prove2.me/submissions/d888824f-c50e-4b87-a3d3-30970f9f3685

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenPolar
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_laplacian_eq_fderiv_fderiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Filter Topology InnerProductSpace
open scoped Laplacian
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open GreenFunction
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {u : ℂ × E → ℝ}
    (hu : ContDiff ℝ 2 u) (z : ℂ) (p : E) :
    Δ (fun w : ℂ => u (w, p)) z = fderiv ℝ (fderiv ℝ u) (z, p) (1, 0) (1, 0)
      + fderiv ℝ (fderiv ℝ u) (z, p) (Complex.I, 0) (Complex.I, 0) := by
  have hd : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  set L : ℂ →L[ℝ] ℂ × E := (ContinuousLinearMap.id ℝ ℂ).prod (0 : ℂ →L[ℝ] E) with hL
  set Ψ : ((ℂ × E) →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ ℂ (ℂ × E) ℝ).flip L with hΨ
  have hpath : ∀ w : ℂ, HasFDerivAt (fun w : ℂ => (w, p)) L w := fun w =>
    (hasFDerivAt_id w).prodMk (hasFDerivAt_const p w)
  have h1 : fderiv ℝ (fun w : ℂ => u (w, p)) = fun w => Ψ (fderiv ℝ u (w, p)) := by
    funext w
    exact ((hd _).hasFDerivAt.comp w (hpath w)).fderiv
  have h2 : HasFDerivAt (fun w : ℂ => Ψ (fderiv ℝ u (w, p)))
      (Ψ.comp ((fderiv ℝ (fderiv ℝ u) (z, p)).comp L)) z :=
    Ψ.hasFDerivAt.comp z ((hd2 _).hasFDerivAt.comp z (hpath z))
  rw [laplacian_eq_fderiv_fderiv, h1, h2.fderiv]
  simp [Ψ, L]
end ReciprocityTheory.AnForm.A
