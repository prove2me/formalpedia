-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.TraceConjugationCover.lv_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:13:24.949377+00:00
-- url     : https://prove2.me/submissions/134008fc-98bb-47fa-b9db-ea69a60c1a5a

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ComplexHessianIsHermitianOfContDiffAt
import Theorems.Thm_ReciprocityTheory_AnForm_A_TraceConjugationCover_lv_add_left
import Theorems.Thm_ReciprocityTheory_AnForm_A_TraceConjugationCover_lv_smul_left
import Theorems.Thm_ReciprocityTheory_AnForm_A_TraceConjugationCover_vec_eq_sum

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
variable {D : ℕ} (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ)
namespace ReciprocityTheory.AnForm.A.TraceConjugationCover
theorem _root_.solution (v b : Fin D → ℂ) :
    lv H v b = ∑ i, v i * lv H (Pi.single i 1) b := by
  let ℓ : (Fin D → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun a => lv H a b
      map_add' := fun a a' => lv_add_left H a a' b
      map_smul' := fun c a => lv_smul_left H c a b }
  have := map_sum ℓ (fun i => v i • (Pi.single i 1 : Fin D → ℂ)) Finset.univ
  rw [← vec_eq_sum] at this
  simp only [map_smul, smul_eq_mul] at this
  exact this
end ReciprocityTheory.AnForm.A.TraceConjugationCover
