-- Prove2me | solution 1 for TunnellMap.GloballyRanked.proposalCount_le_position
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:59:02.149869+00:00
-- url     : https://prove2.me/submissions/38080011-177b-4fa6-9c79-33ace289f550

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_Parking
import Theorems.Thm_TunnellMap_GloballyRanked_proposalCount_le_earlier_add_one
import Theorems.Thm_TunnellMap_GloballyRanked_earlierMatchedSources_card_le_position

set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
omit [DecidableEq S] [DecidableEq T]
namespace TunnellMap.GloballyRanked
theorem _root_.solution (I : GloballyRanked K S T)
    (M : S ≃ T) (hM : I.Stable M)
    (order : Fin (Fintype.card S) ≃ S) (horder : I.MatchedKeyOrder M order)
    (i : Fin (Fintype.card S)) :
    I.proposalCount M (order i) ≤ i.1 + 1 := by
  exact (I.proposalCount_le_earlier_add_one M hM (order i)).trans
    (Nat.add_le_add_right (I.earlierMatchedSources_card_le_position M order horder i) 1)
end TunnellMap.GloballyRanked
