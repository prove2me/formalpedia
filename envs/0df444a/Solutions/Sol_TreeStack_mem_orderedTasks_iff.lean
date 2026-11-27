-- Prove2me | solution 1 for TreeStack.mem_orderedTasks_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:31:48.581038+00:00
-- url     : https://prove2.me/submissions/ff5bef3a-5287-4038-95bd-923f77638cdb

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
theorem _root_.solution (gain : α → ℤ) (tasks : List α) (t : α) :
    t ∈ orderedTasks gain tasks ↔ t ∈ tasks := by
  constructor
  · intro ht
    simp only [orderedTasks, List.mem_append] at ht
    rcases ht with ht | ht
    · have hpos : t ∈ tasks ∧ 0 < gain t := by
        simpa [positiveTasks] using ht
      exact hpos.1
    · rcases ht with ht | ht
      · have hzero : t ∈ tasks ∧ gain t = 0 := by
          simpa [zeroTasks] using ht
        exact hzero.1
      · have hneg : t ∈ tasks ∧ gain t < 0 := by
          simpa [negativeTasks] using ht
        exact hneg.1
  · intro ht
    by_cases hp : 0 < gain t
    · have : t ∈ positiveTasks gain tasks := by
        simpa [positiveTasks, ht, hp]
      exact by
        simp only [orderedTasks, List.mem_append]
        exact Or.inl this
    · by_cases hz : gain t = 0
      · have : t ∈ zeroTasks gain tasks := by
          simpa [zeroTasks, ht, hz]
        exact by
          simp only [orderedTasks, List.mem_append]
          exact Or.inr (Or.inl this)
      · have hn : gain t < 0 := by omega
        have : t ∈ negativeTasks gain tasks := by
          simpa [negativeTasks, ht, hn]
        exact by
          simp only [orderedTasks, List.mem_append]
          exact Or.inr (Or.inr this)
end TreeStack
