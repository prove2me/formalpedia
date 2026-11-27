-- Prove2me | solution 1 for TreeStack.orderedTasks_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:31:49.069628+00:00
-- url     : https://prove2.me/submissions/0a73f1cc-2d2a-417f-b6e7-2752c920b75d

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
import Theorems.Thm_TreeStack_MoveSignature_zero_count
import Theorems.Thm_TreeStack_MoveSignature_incoming_zero
import Theorems.Thm_TreeStack_MoveSignature_outgoing_zero
import Theorems.Thm_TreeStack_MoveSignature_extend_count_same
import Theorems.Thm_TreeStack_F_three
import Theorems.Thm_TreeStack_F_two
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_root
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_empty
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_some
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_root_ne_parent
import Theorems.Thm_TreeStack_empty_ne_integer_zero
import Theorems.Thm_TreeStack_mass_oneOn
import Theorems.Thm_TreeStack_mem_support_iff
import Theorems.Thm_TreeStack_oneOn_apply
attribute [local simp] TreeStack.F_three
attribute [local simp] TreeStack.F_two
attribute [local simp] TreeStack.OrientedBranch.childBranch_parent
attribute [local simp] TreeStack.OrientedBranch.childBranch_root
attribute [local simp] TreeStack.OrientedBranch.messageContribution_empty
attribute [local simp] TreeStack.OrientedBranch.messageContribution_some
attribute [local simp] TreeStack.OrientedBranch.root_mem_vertices
attribute [local simp] TreeStack.OrientedBranch.root_ne_parent
attribute [local simp] TreeStack.empty_ne_integer_zero
attribute [local simp] TreeStack.mass_oneOn
attribute [local simp] TreeStack.mem_support_iff
attribute [local simp] TreeStack.oneOn_apply


attribute [local simp] TreeStack.MoveSignature.zero_count
attribute [local simp] TreeStack.MoveSignature.incoming_zero
attribute [local simp] TreeStack.MoveSignature.outgoing_zero
attribute [local simp] TreeStack.MoveSignature.extend_count_same

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {α : Type*}
namespace TreeStack
theorem _root_.solution (gain : α → ℤ) {tasks : List α}
    (h : tasks.Nodup) :
    (orderedTasks gain tasks).Nodup := by
  rw [orderedTasks]
  have hp := h.filter (fun t => 0 < gain t)
  have hz := h.filter (fun t => gain t = 0)
  have hn := h.filter (fun t => gain t < 0)
  rw [List.nodup_append]
  constructor
  · exact hp
  · constructor
    · rw [List.nodup_append]
      exact ⟨hz, hn, by
        intro a ha b hb hab
        subst b
        have hZeroData : a ∈ tasks ∧ gain a = 0 := by
          simpa [zeroTasks] using ha
        have hNegData : a ∈ tasks ∧ gain a < 0 := by
          simpa [negativeTasks] using hb
        have hZero : gain a = 0 := hZeroData.2
        have hNeg : gain a < 0 := hNegData.2
        omega⟩
    · intro a ha b hb hab
      subst b
      have hPosData : a ∈ tasks ∧ 0 < gain a := by
        simpa [positiveTasks] using ha
      have hPos : 0 < gain a := hPosData.2
      simp only [List.mem_append] at hb
      rcases hb with hZeroMem | hNegMem
      · have hZeroData : a ∈ tasks ∧ gain a = 0 := by
          simpa [zeroTasks] using hZeroMem
        have hZero : gain a = 0 := hZeroData.2
        omega
      · have hNegData : a ∈ tasks ∧ gain a < 0 := by
          simpa [negativeTasks] using hNegMem
        have hNeg : gain a < 0 := hNegData.2
        omega
end TreeStack
