-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.proposalValid_rejectProposal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:37:01.889021+00:00
-- url     : https://prove2.me/submissions/fa194856-3b38-4c34-9c62-f65a2be0a4a3

import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_old_mem_take_after_cursor_advance
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_mem_take_after_cursor_advance_cases
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
    (st : I.DAState) (hv : st.ProposalValid I)
    (s : S) (rest : List S) (h : st.cursor s < Fintype.card T)
    {old : S} (hheld : st.held (st.nextTarget I s h) = some old)
    (hnotbetter : ¬ I.rank s (st.nextTarget I s h) <
      I.rank old (st.nextTarget I s h)) :
    (st.rejectProposal I s rest h).ProposalValid I := by
  let st' := st.rejectProposal I s rest h
  have hself : st'.cursor s = st.cursor s + 1 := by
    simp [st', rejectProposal, advancedCursor]
  have hother : ∀ x, x ≠ s → st'.cursor x = st.cursor x := by
    intro x hx
    simp [st', rejectProposal, advancedCursor, hx]
  constructor
  · intro x t hassigned
    have holdAssigned : st.assigned x = some t := by
      simpa [st', rejectProposal] using hassigned
    exact old_mem_take_after_cursor_advance I st st' s h hself hother
      (hv.assigned_tried x t holdAssigned)
  · intro x t ht
    rcases mem_take_after_cursor_advance_cases I st st' s h hself hother ht with
      hold | hnew
    · obtain ⟨holder, hholder, hkey⟩ := hv.held_dominates x t hold
      exact ⟨holder, by simpa [st', rejectProposal] using hholder, hkey⟩
    · rcases hnew with ⟨hxs, htnew⟩
      subst x
      subst t
      exact ⟨old, by simpa [st', rejectProposal] using hheld,
        le_of_not_gt hnotbetter⟩
end TunnellMap.GloballyRanked.DAState
