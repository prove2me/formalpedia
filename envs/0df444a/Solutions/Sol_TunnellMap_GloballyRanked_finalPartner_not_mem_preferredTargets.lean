-- Prove2me | solution 1 for TunnellMap.GloballyRanked.finalPartner_not_mem_preferredTargets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:04:31.255779+00:00
-- url     : https://prove2.me/submissions/2353e96b-4bfc-49d0-bcbe-eb6c88eb8a1a

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_Parking
import Definitions.Def_TunnellMap_DeferredAcceptance
import Theorems.Thm_TunnellMap_GloballyRanked_finalPartner_mem_proposalTargets
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
    (M : S ≃ T) (s : S) : M s ∉ I.preferredTargets M s := by
  simp [preferredTargets]
end TunnellMap.GloballyRanked
