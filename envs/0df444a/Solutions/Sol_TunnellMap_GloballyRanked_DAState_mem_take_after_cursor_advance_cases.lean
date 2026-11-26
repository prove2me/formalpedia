-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.mem_take_after_cursor_advance_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:34:10.712838+00:00
-- url     : https://prove2.me/submissions/568ce5c6-194a-464d-bf21-a9adb085409a

import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Theorems.Thm_P2M_TunnellMap_GloballyRanked_DAState_nextTarget_getElem__ca19f18bfab1
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_matchingOfTerminal_apply
import Theorems.Thm_TunnellMap_GloballyRanked_finalPartner_mem_proposalTargets
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_GloballyRanked_length_preferenceList
import Theorems.Thm_TunnellMap_GloballyRanked_mem_preferenceList
attribute [local simp] TunnellMap.GloballyRanked.DAState.matchingOfTerminal_apply
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
    (st st' : I.DAState) (s : S)
    (h : st.cursor s < Fintype.card T)
    (hself : st'.cursor s = st.cursor s + 1)
    (hother : ∀ x, x ≠ s → st'.cursor x = st.cursor x)
    {x : S} {t : T}
    (ht : t ∈ (I.preferenceList x).take (st'.cursor x)) :
    t ∈ (I.preferenceList x).take (st.cursor x) ∨
      (x = s ∧ t = st.nextTarget I s h) := by
  by_cases hx : x = s
  · subst x
    rw [hself, List.take_succ, nextTarget_getElem? I st s h] at ht
    simp only [Option.toList_some, List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | ht
    · exact Or.inl ht
    · exact Or.inr ⟨rfl, ht⟩
  · rw [hother x hx] at ht
    exact Or.inl ht
end TunnellMap.GloballyRanked.DAState
