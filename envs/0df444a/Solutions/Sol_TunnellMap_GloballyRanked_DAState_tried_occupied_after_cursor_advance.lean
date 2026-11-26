-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.tried_occupied_after_cursor_advance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:12:14.520803+00:00
-- url     : https://prove2.me/submissions/556411fc-ada6-4311-b157-67ae649b1dc8

import Definitions.Def_TunnellMap_DeferredAcceptanceAlgorithm
import Definitions.Def_TunnellMap_DeferredAcceptanceCorrectness
import Theorems.Thm_P2M_TunnellMap_GloballyRanked_DAState_nextTarget_getElem__ca19f18bfab1
import Theorems.Thm_TunnellMap_GloballyRanked_finalPartner_mem_proposalTargets
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_GloballyRanked_length_preferenceList
import Theorems.Thm_TunnellMap_GloballyRanked_mem_preferenceList
attribute [local simp] TunnellMap.GloballyRanked.finalPartner_mem_proposalTargets
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.length_preferenceList
attribute [local simp] TunnellMap.GloballyRanked.mem_preferenceList



set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)
namespace TunnellMap.GloballyRanked.DAState
theorem _root_.solution
    (st st' : I.DAState) (hv : st.Valid I) (s : S)
    (h : st.cursor s < Fintype.card T)
    (hself : st'.cursor s = st.cursor s + 1)
    (hother : ∀ x, x ≠ s → st'.cursor x = st.cursor x)
    (hmono : ∀ t, st.Occupied I t → st'.Occupied I t)
    (hnext : st'.Occupied I (st.nextTarget I s h)) :
    ∀ x t, t ∈ (I.preferenceList x).take (st'.cursor x) →
      st'.Occupied I t := by
  intro x t ht
  by_cases hx : x = s
  · subst x
    rw [hself, List.take_succ, nextTarget_getElem?] at ht
    simp only [Option.toList_some, List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | ht
    · exact hmono t (hv.tried_occupied s t ht)
    · simpa only [ht] using hnext
  · rw [hother x hx] at ht
    exact hmono t (hv.tried_occupied x t ht)
end TunnellMap.GloballyRanked.DAState
