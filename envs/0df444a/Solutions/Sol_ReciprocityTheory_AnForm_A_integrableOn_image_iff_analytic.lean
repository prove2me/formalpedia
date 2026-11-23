-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.integrableOn_image_iff_analytic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:43.379695+00:00
-- url     : https://prove2.me/submissions/63af89de-3dc3-4056-95fc-9dba0eba1545

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ComplexHessianIsHermitianOfContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Theorems.Thm_ReciprocityTheory_AnForm_A_det_jacC
import Theorems.Thm_ReciprocityTheory_AnForm_A_det_restrictScalars_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Matrix
noncomputable section
variable {D E : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (τ : (Fin D → ℂ) → (Fin D → ℂ)) (U : Set (Fin D → ℂ)) (hU : IsOpen U)
    (hτ : AnalyticOnNhd ℂ τ U) (hinj : Set.InjOn τ U) (f : (Fin D → ℂ) → F) :
    IntegrableOn f (τ '' U) ↔
      IntegrableOn (fun z => Complex.normSq (jacC τ z).det • f (τ z)) U := by
  have hd : ∀ x ∈ U, HasFDerivWithinAt τ ((fderiv ℂ τ x).restrictScalars ℝ) U x :=
    fun x hx => ((hτ x hx).differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hdet : ∀ x, |((fderiv ℂ τ x).restrictScalars ℝ).det| = Complex.normSq (jacC τ x).det := by
    intro x
    rw [det_jacC]
    have e := det_restrictScalars_real (fderiv ℂ τ x : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))
    rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, e,
      abs_of_nonneg (Complex.normSq_nonneg _)]
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hU.measurableSet hd hinj f]
  simp_rw [hdet]
end ReciprocityTheory.AnForm.A
