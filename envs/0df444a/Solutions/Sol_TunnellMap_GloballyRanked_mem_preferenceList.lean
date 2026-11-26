-- Prove2me | solution 1 for TunnellMap.GloballyRanked.mem_preferenceList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:51:03.563059+00:00
-- url     : https://prove2.me/submissions/48ae3f1f-c172-46fa-bef8-c1d5a697666d

import Definitions.Def_TunnellMap_GloballyRanked
import Definitions.Def_TunnellMap_PreferenceList

set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype T] [DecidableEq T]
namespace TunnellMap.GloballyRanked
theorem _root_.solution (I : GloballyRanked K S T) (s : S) (t : T) :
    t ∈ I.preferenceList s := by
  letI : LinearOrder T := LinearOrder.lift' (I.rank s) (I.source_injective s)
  have h : t ∈ (Finset.univ : Finset T).sort (α := T) (· ≤ ·) := by
    simp
  exact h
end TunnellMap.GloballyRanked
