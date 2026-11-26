-- Prove2me | solution 1 for TunnellMap.GloballyRanked.length_matchedProposalCounts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:29:35.673204+00:00
-- url     : https://prove2.me/submissions/512515ec-e38b-469b-b87d-d6584cf5e096

import Definitions.Def_TunnellMap_MatchedOrder
import Definitions.Def_TunnellMap_ParkingRearrangement
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right



set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
namespace TunnellMap.GloballyRanked
theorem _root_.solution
    (I : GloballyRanked K S T) (M : S ≃ T) :
    (I.matchedProposalCounts M).length = Fintype.card S := by
  simp [matchedProposalCounts]
end TunnellMap.GloballyRanked
