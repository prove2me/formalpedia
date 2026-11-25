-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.TraceConjugationCover.complexHessian_comp_holomorphic_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:28:32.011596+00:00
-- url     : https://prove2.me/submissions/35c2718c-eca7-49c7-80cc-106d93124815

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ComplexHessianIsHermitianOfContDiffAt
import Theorems.Thm_ReciprocityTheory_AnForm_A_TraceConjugationCover_hessC_eq_lv
import Theorems.Thm_ReciprocityTheory_AnForm_A_TraceConjugationCover_lv_expand
import Theorems.Thm_ReciprocityTheory_AnForm_A_TraceConjugationCover_lv_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.TraceConjugationCover
open Complex Filter Topology Matrix
noncomputable section
variable {D E : ℕ}
namespace ReciprocityTheory.AnForm.A.TraceConjugationCover
theorem _root_.solution (φ : (Fin E → ℂ) → ℝ) (τ : (Fin D → ℂ) → (Fin E → ℂ)) (z : Fin D → ℂ)
    (hτ : AnalyticAt ℂ τ z) (hφ : ContDiffAt ℝ 2 φ (τ z)) :
    hessC (φ ∘ τ) z = (Matrix.of fun a k => fderiv ℂ τ z (Pi.single k 1) a)ᵀ * hessC φ (τ z) *
      (Matrix.of fun a k => fderiv ℂ τ z (Pi.single k 1) a).map (starRingEnd ℂ) := by
  ext i j
  rw [hessC_eq_lv, lv_comp φ τ z hτ hφ, lv_expand]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply,
    Finset.sum_mul, ← hessC_eq_lv]
  rw [Finset.sum_comm]
end ReciprocityTheory.AnForm.A.TraceConjugationCover
