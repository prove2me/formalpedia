-- Prove2me | solution 1 for TunnellMap.GloballyRanked.sharpProposalCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:44:42.316837+00:00
-- url     : https://prove2.me/submissions/d2d2136b-9d7d-41ee-887c-86d583135231

import Definitions.Def_TunnellMap_ParkingRearrangement
import Definitions.Def_TunnellMap_Sharpness
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_GloballyRanked_length_matchedProposalCounts
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.length_matchedProposalCounts



set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
namespace TunnellMap.GloballyRanked
theorem _root_.solution (m : ℕ) (i : Fin m) :
    (sharpRanking m).proposalCount (sharpMatching m) i = i.1 + 1 := by
  unfold proposalCount preferredTargets
  have hfilter :
      (Finset.univ.filter fun t : Fin m =>
        (sharpRanking m).rank i t <
          (sharpRanking m).rank i (sharpMatching m i)) =
        Finset.univ.filter fun t : Fin m => t.1 < i.1 := by
    ext t
    simp [sharpRanking, sharpRank, sharpMatching]
  rw [hfilter, Fin.card_filter_val_lt,
    Nat.min_eq_right (Nat.le_of_lt i.2)]
end TunnellMap.GloballyRanked
