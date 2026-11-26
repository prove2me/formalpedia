-- Prove2me | solution 1 for TunnellMap.GloballyRanked.proposalTargets_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:06:35.844456+00:00
-- url     : https://prove2.me/submissions/87e1f27b-5abf-45ad-8ebc-d8bf8585890b

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_Parking
import Definitions.Def_TunnellMap_DeferredAcceptance
import Theorems.Thm_TunnellMap_GloballyRanked_finalPartner_mem_proposalTargets
import Theorems.Thm_TunnellMap_GloballyRanked_finalPartner_not_mem_preferredTargets
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
    (M : S ≃ T) (s : S) :
    (I.proposalTargets M s).card = I.proposalCount M s := by
  simp [proposalTargets, proposalCount, I.finalPartner_not_mem_preferredTargets M s]
end TunnellMap.GloballyRanked
