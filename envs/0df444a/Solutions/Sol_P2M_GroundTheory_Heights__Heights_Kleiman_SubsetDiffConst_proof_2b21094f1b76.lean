-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SubsetDiffConst_proof_2b21094f1b76
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:07:50.398817+00:00
-- url     : https://prove2.me/submissions/0f807986-11bb-4b69-b4bc-a6c980dab7f5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StSubsetDiffConst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PSubsetDiffConst
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_subsetDiff_eq_sum_support_020a5c302417
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_sum_exponents_lt_of_mem_support_53993d495681
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_le_sum_of_prod_ne_zero_379ccba448f3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace SubsetDiffConst
theorem _root_.solution : SubsetDiffConst.Statement := by
  intro n f ⟨Q, hQ, hf⟩
  have split : ∀ e : Fin (n + 1 + 1) →₀ ℕ, ∑ j, e j =
      ∑ i : Fin n, e i.castSucc.castSucc + e (Fin.last n).castSucc + e (Fin.last (n + 1)) := fun e => by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  refine ⟨fun m m' c c' => ?_, fun ⟨Q', hQ', hf'⟩ m c => ?_⟩
  · rw [subsetDiff_eq_sum_support n f Q hf, subsetDiff_eq_sum_support n f Q hf]
    refine sum_congr rfl fun e he => ?_
    by_cases hp : (∏ i : Fin n, (1 - (0 : ℚ) ^ e i.castSucc.castSucc)) = 0
    · simp [hp]
    · have h1 := le_sum_of_prod_ne_zero n (fun i => e i.castSucc.castSucc) hp
      have h2 := sum_exponents_lt_of_mem_support hQ he
      rw [split] at h2
      have ha : e (Fin.last n).castSucc = 0 := by omega
      have hb : e (Fin.last (n + 1)) = 0 := by omega
      simp [ha, hb]
  · rw [subsetDiff_eq_sum_support n f Q' hf']
    refine sum_eq_zero fun e he => ?_
    by_cases hp : (∏ i : Fin n, (1 - (0 : ℚ) ^ e i.castSucc.castSucc)) = 0
    · simp [hp]
    · have h1 := le_sum_of_prod_ne_zero n (fun i => e i.castSucc.castSucc) hp
      have h2 := sum_exponents_lt_of_mem_support hQ' he
      rw [split] at h2
      omega
end SubsetDiffConst
end GroundTheory.Heights₂.Heights.Kleiman
