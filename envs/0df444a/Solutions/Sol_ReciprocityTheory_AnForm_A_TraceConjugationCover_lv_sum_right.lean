-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.TraceConjugationCover.lv_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:11:03.629941+00:00
-- url     : https://prove2.me/submissions/fc26e382-b73a-4fcb-8a7d-3340b14c1c20

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ComplexHessianIsHermitianOfContDiffAt
import Theorems.Thm_ReciprocityTheory_AnForm_A_TraceConjugationCover_lv_add_right
import Theorems.Thm_ReciprocityTheory_AnForm_A_TraceConjugationCover_lv_smul_right
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
theorem _root_.solution (a v : Fin D → ℂ) :
    lv H a v = ∑ i, starRingEnd ℂ (v i) * lv H a (Pi.single i 1) := by
  let ℓ : (Fin D → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun b => starRingEnd ℂ (lv H a b)
      map_add' := fun b b' => by simp [lv_add_right]
      map_smul' := fun c b => by simp [lv_smul_right] }
  have := map_sum ℓ (fun i => v i • (Pi.single i 1 : Fin D → ℂ)) Finset.univ
  rw [← vec_eq_sum] at this
  simp only [map_smul, smul_eq_mul] at this
  have h := congrArg (starRingEnd ℂ) this
  simp only [ℓ, LinearMap.coe_mk, AddHom.coe_mk, Complex.conj_conj, map_sum, map_mul] at h
  exact h
end ReciprocityTheory.AnForm.A.TraceConjugationCover
