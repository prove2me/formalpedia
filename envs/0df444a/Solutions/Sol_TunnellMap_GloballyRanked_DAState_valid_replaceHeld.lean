-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.valid_replaceHeld
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:13:29.423383+00:00
-- url     : https://prove2.me/submissions/1f05e3b1-60a5-4e27-a571-6c5fb1076317

import Definitions.Def_TunnellMap_DeferredAcceptanceAlgorithm
import Definitions.Def_TunnellMap_DeferredAcceptanceCorrectness
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_tried_occupied_after_cursor_advance
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
theorem _root_.solution (st : I.DAState) (hv : st.Valid I)
    (s : S) (rest : List S) (hqueue : st.queue = s :: rest)
    (h : st.cursor s < Fintype.card T) (old : S)
    (hheld : st.held (st.nextTarget I s h) = some old) :
    (st.replaceHeld I s rest h old).Valid I := by
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
  have hn := hv.queue_nodup
  rw [hqueue, List.nodup_cons] at hn
  have hsNotRest : s ∉ rest := hn.1
  have holdNotQueue : old ∉ st.queue := by
    intro holdMem
    have holdFree := (hv.queued_iff_unassigned old).mp holdMem
    rw [holdAssigned] at holdFree
    contradiction
  have holdNotRest : old ∉ rest := by
    intro holdMem
    exact holdNotQueue (by simp [hqueue, holdMem])
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (rest ++ [old]).Nodup
    rw [List.nodup_append]
    refine ⟨hn.2, by simp, ?_⟩
    intro a ha b hb
    have hbEq : b = old := by simpa using hb
    subst b
    exact fun hao => holdNotRest (hao ▸ ha)
  · intro x
    have hold := hv.queued_iff_unassigned x
    rw [hqueue] at hold
    by_cases hxs : x = s
    · subst x
      simp [replaceHeld, hsNotRest, hso]
    · by_cases hxo : x = old
      · subst x
        simp [replaceHeld, Ne.symm hso]
      · simpa [replaceHeld, hxs, hxo] using hold
  · intro x u
    by_cases hu : u = st.nextTarget I s h
    · subst u
      by_cases hxs : x = s
      · subst x
        simp [replaceHeld]
      · constructor
        · intro hnewHeld
          simp [replaceHeld] at hnewHeld
          exact (hxs hnewHeld.symm).elim
        · intro hnewAssigned
          by_cases hxo : x = old
          · subst x
            simp [replaceHeld, Ne.symm hso] at hnewAssigned
          · have holdX : st.assigned x =
                some (st.nextTarget I s h) := by
              simpa [replaceHeld, hxs, hxo] using hnewAssigned
            have hheldX :=
              (hv.held_iff_assigned x (st.nextTarget I s h)).mpr holdX
            have hxOld : x = old := Option.some.inj (hheldX.symm.trans hheld)
            exact (hxo hxOld).elim
    · by_cases hxs : x = s
      · subst x
        constructor
        · intro hnewHeld
          have holdHeld : st.held u = some s := by
            simpa [replaceHeld, hu] using hnewHeld
          have holdSource := (hv.held_iff_assigned s u).mp holdHeld
          rw [hsFree] at holdSource
          contradiction
        · intro hnewAssigned
          have htargetEq : st.nextTarget I s h = u := by
            simpa [replaceHeld] using hnewAssigned
          exact (hu htargetEq.symm).elim
      · by_cases hxo : x = old
        · subst x
          constructor
          · intro hnewHeld
            have holdHeld : st.held u = some old := by
              simpa [replaceHeld, hu] using hnewHeld
            have holdSource := (hv.held_iff_assigned old u).mp holdHeld
            have huEq : u = st.nextTarget I s h :=
              Option.some.inj (holdSource.symm.trans holdAssigned)
            exact (hu huEq).elim
          · intro hnewAssigned
            simp [replaceHeld, Ne.symm hso] at hnewAssigned
        · simpa [replaceHeld, hu, hxs, hxo] using
            hv.held_iff_assigned x u
  · apply tried_occupied_after_cursor_advance I st
      (st.replaceHeld I s rest h old) hv s h
    · simp [replaceHeld, advancedCursor]
    · intro x hx
      simp [replaceHeld, advancedCursor, hx]
    · intro u hu
      rcases hu with ⟨x, hx⟩
      by_cases hut : u = st.nextTarget I s h
      · subst u
        exact ⟨s, by simp [replaceHeld]⟩
      · exact ⟨x, by simpa [replaceHeld, hut] using hx⟩
    · exact ⟨s, by simp [replaceHeld]⟩
end TunnellMap.GloballyRanked.DAState
