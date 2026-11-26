-- Prove2me | solution 1 for TunnellMap.GloballyRanked.proposalCount_total_le_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:10:52.685588+00:00
-- url     : https://prove2.me/submissions/0b20b6d7-8adf-4826-8e9c-4f2bb660ac2c

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_Parking
import Definitions.Def_TunnellMap_DeferredAcceptance
import Theorems.Thm_TunnellMap_GloballyRanked_finalPartner_mem_proposalTargets
import Theorems.Thm_TunnellMap_GloballyRanked_proposalCount_le_card
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right


attribute [local simp] TunnellMap.GloballyRanked.finalPartner_mem_proposalTargets

set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K]
variable [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
namespace TunnellMap.GloballyRanked
theorem _root_.solution (I : GloballyRanked K S T)
    (M : S ≃ T) :
    (∑ s : S, I.proposalCount M s) ≤ Fintype.card S * Fintype.card T := by
  calc
    (∑ s : S, I.proposalCount M s) ≤ ∑ _s : S, Fintype.card T :=
      Finset.sum_le_sum fun s _ => I.proposalCount_le_card M s
    _ = Fintype.card S * Fintype.card T := by simp
end TunnellMap.GloballyRanked
