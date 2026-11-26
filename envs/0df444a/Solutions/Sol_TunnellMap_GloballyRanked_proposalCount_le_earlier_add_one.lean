-- Prove2me | solution 1 for TunnellMap.GloballyRanked.proposalCount_le_earlier_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:52:54.908562+00:00
-- url     : https://prove2.me/submissions/33cf14e0-d472-4f70-9c7a-c96d93484ce0

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_Parking
import Theorems.Thm_TunnellMap_GloballyRanked_preferredToEarlier_injective
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right



set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
omit [DecidableEq S] [DecidableEq T]
namespace TunnellMap.GloballyRanked
theorem _root_.solution (I : GloballyRanked K S T)
    (M : S ≃ T) (hM : I.Stable M) (s : S) :
    I.proposalCount M s ≤ (I.earlierMatchedSources M s).card + 1 := by
  have hcard : (I.preferredTargets M s).card ≤
      (I.earlierMatchedSources M s).card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective (I.preferredToEarlier M hM s)
        (I.preferredToEarlier_injective M hM s)
  exact Nat.add_le_add_right hcard 1
end TunnellMap.GloballyRanked
