-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.maInt_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:24:31.2963+00:00
-- url     : https://prove2.me/submissions/6f6c4a86-11cc-481f-91ff-c73e64a1504b

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ComplexHessianIsHermitianOfContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Theorems.Thm_ReciprocityTheory_AnForm_A_maDens_comp
import Theorems.Thm_ReciprocityTheory_AnForm_A_integral_image_eq_integral_normSq_det_smul

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
theorem _root_.solution (φ : Fin D → (Fin D → ℂ) → ℝ) (g : (Fin D → ℂ) → ℝ)
    (τ : (Fin D → ℂ) → (Fin D → ℂ)) (U U' : Set (Fin D → ℂ)) (hU : IsOpen U) (hU' : IsOpen U')
    (hτ : AnalyticOnNhd ℂ τ U) (hinj : Set.InjOn τ U) (himg : τ '' U = U')
    (hφ : ∀ k, ContDiffOn ℝ 2 (φ k) U') :
    maInt (fun k => φ k ∘ τ) (g ∘ τ) U = maInt φ g U' := by
  unfold maInt
  rw [← himg, integral_image_eq_integral_normSq_det_smul τ U hU hτ hinj]
  first
    | apply setIntegral_congr_fun hU.measurableSet
    | apply setIntegral_congr hU.measurableSet
  intro z hz
  have hz' : τ z ∈ U' := himg ▸ Set.mem_image_of_mem τ hz
  have hc : ∀ k, ContDiffAt ℝ 2 (φ k) (τ z) := fun k => (hφ k).contDiffAt (hU'.mem_nhds hz')
  simp only [Function.comp_apply, smul_eq_mul]
  rw [maDens_comp φ τ z (hτ z hz) hc]
  ring
end ReciprocityTheory.AnForm.A
