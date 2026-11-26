-- Prove2me | solution 1 for TunnellMap.GloballyRanked.sharpMatching_stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:45:27.010106+00:00
-- url     : https://prove2.me/submissions/3e04797c-0a04-43ff-bb5a-511b8d3ddd59

import Definitions.Def_TunnellMap_ParkingRearrangement
import Definitions.Def_TunnellMap_Sharpness

set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
namespace TunnellMap.GloballyRanked
theorem _root_.solution (m : ℕ) :
    (sharpRanking m).Stable (sharpMatching m) := by
  intro s t hblock
  rcases hblock with ⟨hsource, htarget⟩
  have hts : t.1 < s.1 := by
    change (m + 1) * s.1 + t.1 < (m + 1) * s.1 + s.1 at hsource
    exact Nat.lt_of_add_lt_add_left hsource
  have hmul : (m + 1) * s.1 < (m + 1) * t.1 := by
    change (m + 1) * s.1 + t.1 < (m + 1) * t.1 + t.1 at htarget
    exact Nat.lt_of_add_lt_add_right htarget
  have hst : s.1 < t.1 :=
    (Nat.mul_lt_mul_left (by omega : 0 < m + 1)).mp hmul
  exact (Nat.not_lt_of_ge hts.le) hst
end TunnellMap.GloballyRanked
