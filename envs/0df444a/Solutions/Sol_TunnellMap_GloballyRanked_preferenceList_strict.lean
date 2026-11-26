-- Prove2me | solution 1 for TunnellMap.GloballyRanked.preferenceList_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:58:45.869799+00:00
-- url     : https://prove2.me/submissions/51e8bea4-6e33-46d1-aa63-863209badad6

import Definitions.Def_TunnellMap_GloballyRanked
import Definitions.Def_TunnellMap_PreferenceList
import Theorems.Thm_TunnellMap_GloballyRanked_preferenceList_pairwise
import Theorems.Thm_TunnellMap_GloballyRanked_preferenceList_nodup

set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype T] [DecidableEq T]
namespace TunnellMap.GloballyRanked
theorem _root_.solution (I : GloballyRanked K S T) (s : S)
    {i j : Fin (I.preferenceList s).length} (hij : i < j) :
    I.rank s ((I.preferenceList s).get i) <
      I.rank s ((I.preferenceList s).get j) := by
  have hle := (I.preferenceList_pairwise s).rel_get_of_lt hij
  have htne : (I.preferenceList s).get i ≠ (I.preferenceList s).get j := by
    intro h
    exact (ne_of_lt hij) ((I.preferenceList_nodup s).injective_get h)
  apply lt_of_le_of_ne hle
  intro hrank
  exact htne (I.source_injective s hrank)
end TunnellMap.GloballyRanked
