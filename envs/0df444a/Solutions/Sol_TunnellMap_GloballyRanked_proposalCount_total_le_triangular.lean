-- Prove2me | solution 1 for TunnellMap.GloballyRanked.proposalCount_total_le_triangular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:44:47.992018+00:00
-- url     : https://prove2.me/submissions/c58fff61-6ace-4116-a7bd-563b047453f2

import Definitions.Def_TunnellMap_ParkingTotal
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_TunnellMap_MatchedOrder
import Theorems.Thm_TunnellMap_GloballyRanked_matchedKeyOrderEquiv_spec
import Theorems.Thm_TunnellMap_GloballyRanked_proposalCount_total_le


set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
namespace TunnellMap.GloballyRanked
theorem _root_.solution (I : GloballyRanked K S T)
    (M : S ≃ T) (hM : I.Stable M) :
    (∑ s : S, I.proposalCount M s) ≤
      Fintype.card S * (Fintype.card S + 1) / 2 :=
  I.proposalCount_total_le M hM (I.matchedKeyOrderEquiv M)
    (I.matchedKeyOrderEquiv_spec M)
end TunnellMap.GloballyRanked
