-- Prove2me | solution 1 for TunnellMap.GloballyRanked.preferenceIndex_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:59:42.000068+00:00
-- url     : https://prove2.me/submissions/a9ca7350-ae6a-4e4f-bdbf-51bfa6f86dfc

import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_Parking
import Definitions.Def_TunnellMap_PreferenceListPosition
import Theorems.Thm_TunnellMap_GloballyRanked_get_preferenceIndex
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_GloballyRanked_length_preferenceList
import Theorems.Thm_TunnellMap_GloballyRanked_mem_preferenceList
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.length_preferenceList
attribute [local simp] TunnellMap.GloballyRanked.mem_preferenceList


attribute [local simp] TunnellMap.GloballyRanked.get_preferenceIndex

set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
namespace TunnellMap.GloballyRanked
theorem _root_.solution (I : GloballyRanked K S T) (s : S) :
    Function.Injective (I.preferenceIndex s) := by
  intro t₁ t₂ h
  have hget := congrArg (fun i => (I.preferenceList s).get i) h
  calc
    t₁ = (I.preferenceList s).get (I.preferenceIndex s t₁) :=
      (I.get_preferenceIndex s t₁).symm
    _ = (I.preferenceList s).get (I.preferenceIndex s t₂) := hget
    _ = t₂ := I.get_preferenceIndex s t₂
end TunnellMap.GloballyRanked
