-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.valid_acceptEmpty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:13:25.044891+00:00
-- url     : https://prove2.me/submissions/322f82aa-7ac9-4631-9509-45c92ed7e09e

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
    (h : st.cursor s < Fintype.card T)
    (hempty : st.held (st.nextTarget I s h) = none) :
    (st.acceptEmpty I s rest h).Valid I := by
  have hsMem : s ∈ st.queue := by simp [hqueue]
  have hsFree : st.assigned s = none :=
    (hv.queued_iff_unassigned s).mp hsMem
  have hn := hv.queue_nodup
  rw [hqueue, List.nodup_cons] at hn
  have hsNotRest : s ∉ rest := hn.1
  refine ⟨hn.2, ?_, ?_, ?_⟩
  · intro x
    have hold := hv.queued_iff_unassigned x
    rw [hqueue] at hold
    by_cases hx : x = s
    · subst x
      simp [acceptEmpty, hsNotRest]
    · simpa [acceptEmpty, hx] using hold
  · intro x u
    by_cases hu : u = st.nextTarget I s h
    · subst u
      by_cases hx : x = s
      · subst x
        simp [acceptEmpty]
      · constructor
        · intro hheld
          simp [acceptEmpty, hx] at hheld
          exact (hx hheld.symm).elim
        · intro hassigned
          have holdAssigned : st.assigned x =
              some (st.nextTarget I s h) := by
            simpa [acceptEmpty, hx] using hassigned
          have holdHeld :=
            (hv.held_iff_assigned x (st.nextTarget I s h)).mpr holdAssigned
          rw [hempty] at holdHeld
          contradiction
    · by_cases hx : x = s
      · subst x
        constructor
        · intro hheld
          have holdAssigned := (hv.held_iff_assigned s u).mp (by
            simpa [acceptEmpty, hu] using hheld)
          rw [hsFree] at holdAssigned
          contradiction
        · intro hassigned
          simp [acceptEmpty, hu] at hassigned
          exact (hu hassigned.symm).elim
      · simpa [acceptEmpty, hu, hx] using hv.held_iff_assigned x u
  · apply tried_occupied_after_cursor_advance I st
      (st.acceptEmpty I s rest h) hv s h
    · simp [acceptEmpty, advancedCursor]
    · intro x hx
      simp [acceptEmpty, advancedCursor, hx]
    · intro u hu
      rcases hu with ⟨x, hx⟩
      by_cases hut : u = st.nextTarget I s h
      · subst u
        exact ⟨s, by simp [acceptEmpty]⟩
      · exact ⟨x, by simpa [acceptEmpty, hut] using hx⟩
    · exact ⟨s, by simp [acceptEmpty]⟩
end TunnellMap.GloballyRanked.DAState
