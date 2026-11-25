-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.maDens_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:43:32.813305+00:00
-- url     : https://prove2.me/submissions/44cb1bc5-3dab-45a2-a7c9-4aabfa25a39e

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ComplexHessianIsHermitianOfContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_comp
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_transpose_mul_mul_conj


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
theorem _root_.solution (φ : Fin D → (Fin D → ℂ) → ℝ) (τ : (Fin D → ℂ) → (Fin D → ℂ))
    (z : Fin D → ℂ) (hτ : AnalyticAt ℂ τ z) (hφ : ∀ k, ContDiffAt ℝ 2 (φ k) (τ z)) :
    maDens (fun k => φ k ∘ τ) z = maDens φ (τ z) * Complex.normSq (jacC τ z).det := by
  have h : (fun k => hessC (φ k ∘ τ) z) =
      fun k => (jacC τ z)ᵀ * hessC (φ k) (τ z) * (jacC τ z).map (starRingEnd ℂ) :=
    funext fun k => hessC_comp (φ k) τ z hτ (hφ k)
  simp only [maDens]
  rw [h, mdisc_transpose_mul_mul_conj, Complex.re_ofReal_mul]
  ring
end ReciprocityTheory.AnForm.A
