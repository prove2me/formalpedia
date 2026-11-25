-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagInjSumBound_finset_sum_bound_cc3c3372d6d6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:51:47.925126+00:00
-- url     : https://prove2.me/submissions/16ea87fa-b1f0-46ca-a958-5b3df17754a3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagInjSumBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace FlagInjSumBound
theorem _root_.solution (S : Finset ℕ) :
    ∑ i ∈ Finset.range S.card, i ≤ ∑ x ∈ S, x ∧
      (∑ x ∈ S, x = ∑ i ∈ Finset.range S.card, i → S ⊆ Finset.range S.card) := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert m S' hlt ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    have hm : m ∉ S' := fun h => lt_irrefl m (hlt m h)
    have hsub : S' ⊆ Finset.range m := fun x hx => Finset.mem_range.2 (hlt x hx)
    have hcard : S'.card ≤ m := by simpa using Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hm, Finset.sum_range_succ, Finset.sum_insert hm]
    refine ⟨by omega, fun heq => ?_⟩
    have hmeq : m = S'.card := by omega
    have hS' := ih₂ (by omega)
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact Finset.mem_range.2 (by omega)
    · exact Finset.mem_range.2 (Nat.lt_succ_of_lt (Finset.mem_range.1 (hS' hx)))
end FlagInjSumBound
end GroundTheory.Heights₂.Heights.RestTerms
