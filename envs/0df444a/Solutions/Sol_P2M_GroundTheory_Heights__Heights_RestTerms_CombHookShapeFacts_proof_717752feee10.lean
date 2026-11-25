-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CombHookShapeFacts_proof_717752feee10
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:34:08.572889+00:00
-- url     : https://prove2.me/submissions/6e8b6a3e-68ae-427c-8b61-2d3925a9a73d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombHookShapeFacts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CombHookShapeFacts_sum_lt_indicator_c8e6898ca902

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open Finset
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace CombHookShapeFacts
theorem _root_.solution : CombHookShapeFacts.Statement := by
  intro r s l hls hsr
  refine ⟨?_, ?_⟩
  · intro i j hij
    have hij' : (i : ℕ) ≤ j := hij
    simp only [hookShape]
    split_ifs <;> omega
  · obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    have h := Fin.sum_univ_eq_sum_range
      (fun k : ℕ => if k = 0 then s - l else if k ≤ l then 1 else 0) (m + 1)
    simp only [hookShape]
    rw [h, sum_range_succ']
    have h2 : (∑ i ∈ range m, (if i + 1 = 0 then s - l else if i + 1 ≤ l then 1 else 0)) =
        ∑ i ∈ range m, (if i < l then 1 else 0) := by
      refine sum_congr rfl fun i _ => ?_
      rw [if_neg (Nat.succ_ne_zero i)]
      split_ifs <;> omega
    rw [h2, CombHookShapeFacts.sum_lt_indicator l m]
    simp only [if_true]
    omega
end CombHookShapeFacts
end GroundTheory.Heights₂.Heights.RestTerms
