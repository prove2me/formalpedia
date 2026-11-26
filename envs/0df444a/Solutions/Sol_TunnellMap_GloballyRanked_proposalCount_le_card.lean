-- Prove2me | solution 1 for TunnellMap.GloballyRanked.proposalCount_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:08:29.381248+00:00
-- url     : https://prove2.me/submissions/2cffdf14-0e4d-488b-9689-248b805c0de5

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_Parking
import Definitions.Def_TunnellMap_DeferredAcceptance
import Theorems.Thm_TunnellMap_GloballyRanked_proposalTargets_card

set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K]
variable [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
namespace TunnellMap.GloballyRanked
theorem _root_.solution (I : GloballyRanked K S T)
    (M : S ≃ T) (s : S) : I.proposalCount M s ≤ Fintype.card T := by
  rw [← I.proposalTargets_card M s, ← Finset.card_univ]
  exact Finset.card_le_card (Finset.subset_univ _)
end TunnellMap.GloballyRanked
