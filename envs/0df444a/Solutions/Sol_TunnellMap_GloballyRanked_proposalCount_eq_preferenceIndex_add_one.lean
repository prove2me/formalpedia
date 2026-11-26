-- Prove2me | solution 1 for TunnellMap.GloballyRanked.proposalCount_eq_preferenceIndex_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:43:14.504251+00:00
-- url     : https://prove2.me/submissions/87d6fb53-35ec-4f7f-9b20-fa434ae40ba4

import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_Parking
import Definitions.Def_TunnellMap_PreferenceListPosition
import Theorems.Thm_TunnellMap_GloballyRanked_preferredTargets_card_eq_preferenceIndex

set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
namespace TunnellMap.GloballyRanked
theorem _root_.solution
    (I : GloballyRanked K S T) (M : S ≃ T) (s : S) :
    I.proposalCount M s = (I.preferenceIndex s (M s)).1 + 1 := by
  rw [proposalCount, I.preferredTargets_card_eq_preferenceIndex M s]
end TunnellMap.GloballyRanked
