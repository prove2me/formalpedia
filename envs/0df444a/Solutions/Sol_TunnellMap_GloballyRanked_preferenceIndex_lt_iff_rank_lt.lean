-- Prove2me | solution 1 for TunnellMap.GloballyRanked.preferenceIndex_lt_iff_rank_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:02:17.979169+00:00
-- url     : https://prove2.me/submissions/c507a669-3924-444e-8d07-9fbca7fde972

import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_Parking
import Definitions.Def_TunnellMap_PreferenceListPosition
import Theorems.Thm_TunnellMap_GloballyRanked_get_preferenceIndex
import Theorems.Thm_TunnellMap_GloballyRanked_preferenceIndex_injective
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_GloballyRanked_length_preferenceList
import Theorems.Thm_TunnellMap_GloballyRanked_mem_preferenceList
import Theorems.Thm_TunnellMap_GloballyRanked_preferenceList_strict
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
theorem _root_.solution (I : GloballyRanked K S T)
    (s : S) (t u : T) :
    I.preferenceIndex s t < I.preferenceIndex s u ↔
      I.rank s t < I.rank s u := by
  constructor
  · intro hidx
    have hstrict := I.preferenceList_strict s hidx
    rw [I.get_preferenceIndex s t, I.get_preferenceIndex s u] at hstrict
    exact hstrict
  · intro hrank
    by_contra hnot
    have hui : I.preferenceIndex s u ≤ I.preferenceIndex s t :=
      le_of_not_gt hnot
    rcases hui.eq_or_lt with heq | hlt
    · have htu : t = u := I.preferenceIndex_injective s heq.symm
      subst u
      exact (lt_irrefl _ hrank).elim
    · have hreverse := I.preferenceList_strict s hlt
      rw [I.get_preferenceIndex s u, I.get_preferenceIndex s t] at hreverse
      have : I.rank s u < I.rank s t := hreverse
      exact (not_lt_of_ge hrank.le) this
end TunnellMap.GloballyRanked
