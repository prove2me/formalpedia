-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.assignedLast_replaceHeld
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:44:07.32834+00:00
-- url     : https://prove2.me/submissions/75a8e327-c2a5-44ed-8a53-5249efa932c8

import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Definitions.Def_TunnellMap_PreferenceListPosition
import Definitions.Def_TunnellMap_MatchedOrder
import Definitions.Def_TunnellMap_DeferredAcceptanceAccounting
import Theorems.Thm_P2M_TunnellMap_GloballyRanked_DAState_nextTarget_getElem__ca19f18bfab1
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_matchingOfTerminal_apply
import Theorems.Thm_TunnellMap_GloballyRanked_finalPartner_mem_proposalTargets
import Theorems.Thm_TunnellMap_GloballyRanked_get_preferenceIndex
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_GloballyRanked_length_preferenceList
import Theorems.Thm_TunnellMap_GloballyRanked_mem_preferenceList
attribute [local simp] TunnellMap.GloballyRanked.DAState.matchingOfTerminal_apply
attribute [local simp] TunnellMap.GloballyRanked.finalPartner_mem_proposalTargets
attribute [local simp] TunnellMap.GloballyRanked.get_preferenceIndex
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
theorem _root_.solution (st : I.DAState)
    (hv : st.Valid I) (hlast : st.AssignedLast I)
    (s : S) (rest : List S) (hqueue : st.queue = s :: rest)
    (h : st.cursor s < Fintype.card T) (old : S)
    (hheld : st.held (st.nextTarget I s h) = some old) :
    (st.replaceHeld I s rest h old).AssignedLast I := by
  have hsMem : s ∈ st.queue := by simp [hqueue]
  have hsFree : st.assigned s = none :=
    (hv.queued_iff_unassigned s).mp hsMem
  have holdAssigned : st.assigned old = some (st.nextTarget I s h) :=
    (hv.held_iff_assigned old (st.nextTarget I s h)).mp hheld
  have hso : s ≠ old := by
    intro hEq
    have hEqAssigned : st.assigned s = st.assigned old :=
      congrArg st.assigned hEq
    have hSome : st.assigned s = some (st.nextTarget I s h) :=
      hEqAssigned.trans holdAssigned
    rw [hsFree] at hSome
    contradiction
  intro x t hassigned
  by_cases hxs : x = s
  · subst x
    have ht : st.nextTarget I s h = t := by
      simpa [replaceHeld, Ne.symm hso] using hassigned
    subst t
    constructor
    · simp [replaceHeld, advancedCursor]
    · simpa [replaceHeld, advancedCursor] using
        nextTarget_getElem? I st s h
  · by_cases hxo : x = old
    · subst x
      simp [replaceHeld, hxs] at hassigned
    · have hold : st.assigned x = some t := by
        simpa [replaceHeld, hxs, hxo] using hassigned
      have hlastOld := hlast x t hold
      simpa [replaceHeld, advancedCursor, hxs] using hlastOld
end TunnellMap.GloballyRanked.DAState
