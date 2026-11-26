-- Prove2me | solution 1 for TunnellMap.GloballyRanked.sharpProposalCount_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:21:27.092463+00:00
-- url     : https://prove2.me/submissions/e1d2a454-18a5-45ac-9cc1-054b4dc9f374

import Definitions.Def_TunnellMap_ParkingRearrangement
import Definitions.Def_TunnellMap_Sharpness
import Theorems.Thm_TunnellMap_GloballyRanked_sharpProposalCount_total_mul_two

set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
namespace TunnellMap.GloballyRanked
theorem _root_.solution (m : ℕ) :
    (∑ i : Fin m,
      (sharpRanking m).proposalCount (sharpMatching m) i) =
        m * (m + 1) / 2 := by
  apply Nat.eq_div_of_mul_eq_left (by norm_num : 2 ≠ 0)
  exact sharpProposalCount_total_mul_two m
end TunnellMap.GloballyRanked
