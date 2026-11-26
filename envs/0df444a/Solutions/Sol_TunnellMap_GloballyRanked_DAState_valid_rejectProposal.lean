-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.valid_rejectProposal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:13:26.741455+00:00
-- url     : https://prove2.me/submissions/e09e146e-6e85-428c-89c6-da2d4490dfec

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
    {old : S} (hheld : st.held (st.nextTarget I s h) = some old) :
    (st.rejectProposal I s rest h).Valid I := by
  have hn := hv.queue_nodup
  rw [hqueue, List.nodup_cons] at hn
  have hsNotRest : s ∉ rest := hn.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (rest ++ [s]).Nodup
    rw [List.nodup_append]
    refine ⟨hn.2, by simp, ?_⟩
    intro a ha b hb
    have hbEq : b = s := by simpa using hb
    subst b
    exact fun has => hsNotRest (has ▸ ha)
  · intro x
    have hold := hv.queued_iff_unassigned x
    rw [hqueue] at hold
    simpa [rejectProposal, or_comm] using hold
  · intro x u
    simpa [rejectProposal] using hv.held_iff_assigned x u
  · apply tried_occupied_after_cursor_advance I st
      (st.rejectProposal I s rest h) hv s h
    · simp [rejectProposal, advancedCursor]
    · intro x hx
      simp [rejectProposal, advancedCursor, hx]
    · intro u hu
      simpa [Occupied, rejectProposal] using hu
    · exact ⟨old, by simpa [rejectProposal] using hheld⟩
end TunnellMap.GloballyRanked.DAState
