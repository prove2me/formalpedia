-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.leviOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:08.422231+00:00
-- url     : https://prove2.me/submissions/1da206d4-85d3-4a4f-a015-77da29c6546d

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
theorem _root_.solution (u : ℂ → ℝ) (z : ℂ) :
    ReciprocityTheory.AnForm.levi (fun w : Fin 1 → ℂ => u (w 0)) (fun _ => z) (Pi.single 0 1) =
      Δ u z / 4 := by
  set e0 : (Fin 1 → ℂ) ≃L[ℝ] ℂ := ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℂ with he0
  set Φ : (ℂ →L[ℝ] ℝ) ≃L[ℝ] ((Fin 1 → ℂ) →L[ℝ] ℝ) :=
    e0.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ) with hΦ
  have h1 : (fun w : Fin 1 → ℂ => u (w 0)) = u ∘ e0 := rfl
  have h2 : fderiv ℝ (u ∘ e0) = Φ ∘ (fderiv ℝ u ∘ e0) := by
    funext w
    rw [e0.comp_right_fderiv]
    ext v
    simp [Φ]
  have h3 : ∀ x, fderiv ℝ (Φ ∘ (fderiv ℝ u ∘ e0)) x =
      (Φ : (ℂ →L[ℝ] ℝ) →L[ℝ] ((Fin 1 → ℂ) →L[ℝ] ℝ)).comp
        ((fderiv ℝ (fderiv ℝ u) (e0 x)).comp (e0 : (Fin 1 → ℂ) →L[ℝ] ℂ)) := fun x => by
    rw [Φ.comp_fderiv, e0.comp_right_fderiv]
  simp only [ReciprocityTheory.AnForm.levi, h1, h2, h3, laplacian_eq_fderiv_fderiv]
  simp [Φ, e0]
end ReciprocityTheory.AnForm.A
