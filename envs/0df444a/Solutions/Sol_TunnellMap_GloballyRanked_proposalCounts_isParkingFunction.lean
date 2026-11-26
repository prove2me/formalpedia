-- Prove2me | solution 1 for TunnellMap.GloballyRanked.proposalCounts_isParkingFunction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:44:52.439237+00:00
-- url     : https://prove2.me/submissions/39066f92-557e-4b2e-a419-3fcef143e4e2

import Definitions.Def_TunnellMap_MatchedOrder
import Definitions.Def_TunnellMap_ParkingRearrangement
import Theorems.Thm_TunnellMap_isParkingFunction_of_indexed_bounds
import Theorems.Thm_TunnellMap_GloballyRanked_length_matchedProposalCounts
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_GloballyRanked_matchedKeyOrderEquiv_spec
import Theorems.Thm_TunnellMap_GloballyRanked_proposalCount_le_position
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right


attribute [local simp] TunnellMap.GloballyRanked.length_matchedProposalCounts

set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
namespace TunnellMap.GloballyRanked
theorem _root_.solution (I : GloballyRanked K S T)
    (M : S ≃ T) (hM : I.Stable M) :
    IsParkingFunction (I.matchedProposalCounts M) := by
  apply isParkingFunction_of_indexed_bounds
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    simp [matchedProposalCounts, proposalCount]
  · intro i
    let j : Fin (Fintype.card S) :=
      ⟨i.1, by simpa using i.2⟩
    have hle := I.proposalCount_le_position M hM
      (I.matchedKeyOrderEquiv M) (I.matchedKeyOrderEquiv_spec M) j
    have hget : (I.matchedProposalCounts M).get i =
        I.proposalCount M (I.matchedKeyOrderEquiv M j) :=
      List.get_ofFn (fun k : Fin (Fintype.card S) =>
        I.proposalCount M (I.matchedKeyOrderEquiv M k)) i
    exact hget.trans_le hle
end TunnellMap.GloballyRanked
