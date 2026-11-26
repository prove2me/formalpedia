-- Prove2me | solution 1 for TunnellMap.GloballyRanked.get_preferenceIndex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:51:41.372435+00:00
-- url     : https://prove2.me/submissions/609d2536-b5a7-4f7a-949f-4f53aa17e9d8

import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_Parking
import Definitions.Def_TunnellMap_PreferenceListPosition
import Theorems.Thm_TunnellMap_GloballyRanked_mem_preferenceList
attribute [local simp] TunnellMap.GloballyRanked.mem_preferenceList



set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
namespace TunnellMap.GloballyRanked
theorem _root_.solution (I : GloballyRanked K S T)
    (s : S) (t : T) :
    (I.preferenceList s).get (I.preferenceIndex s t) = t :=
  Classical.choose_spec (List.get_of_mem (I.mem_preferenceList s t))
end TunnellMap.GloballyRanked
