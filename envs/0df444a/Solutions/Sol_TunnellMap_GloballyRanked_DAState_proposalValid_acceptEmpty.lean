-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.proposalValid_acceptEmpty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:37:01.251267+00:00
-- url     : https://prove2.me/submissions/6cf4f582-20b0-4c8a-b109-1af16c48efee

import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_old_mem_take_after_cursor_advance
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_new_mem_take_after_cursor_advance
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
    (hempty : st.held (st.nextTarget I s h) = none) :
    (st.acceptEmpty I s rest h).ProposalValid I := by
  let st' := st.acceptEmpty I s rest h
  have hself : st'.cursor s = st.cursor s + 1 := by
    simp [st', acceptEmpty, advancedCursor]
  have hother : ∀ x, x ≠ s → st'.cursor x = st.cursor x := by
    intro x hx
    simp [st', acceptEmpty, advancedCursor, hx]
  constructor
  · intro x t hassigned
    by_cases hx : x = s
    · subst x
      have hsome : some (st.nextTarget I s h) = some t := by
        simpa [st', acceptEmpty] using hassigned
      have ht : t = st.nextTarget I s h := (Option.some.inj hsome).symm
      subst t
      exact new_mem_take_after_cursor_advance I st st' s h hself
    · have holdAssigned : st.assigned x = some t := by
        simpa [st', acceptEmpty, hx] using hassigned
      exact old_mem_take_after_cursor_advance I st st' s h hself hother
        (hv.assigned_tried x t holdAssigned)
  · intro x t ht
    rcases mem_take_after_cursor_advance_cases I st st' s h hself hother ht with
      hold | hnew
    · obtain ⟨holder, hheld, hkey⟩ := hv.held_dominates x t hold
      by_cases hut : t = st.nextTarget I s h
      · subst t
        rw [hempty] at hheld
        contradiction
      · exact ⟨holder, by simpa [st', acceptEmpty, hut] using hheld, hkey⟩
    · rcases hnew with ⟨hxs, htnew⟩
      subst x
      subst t
      exact ⟨s, by simp [st', acceptEmpty], le_rfl⟩
end TunnellMap.GloballyRanked.DAState
