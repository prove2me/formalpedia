-- Prove2me | solution 1 for TreeStack.OrientedBranch.taskGainSum_occupiedChildTasks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:42:29.6743+00:00
-- url     : https://prove2.me/submissions/b14d9a3b-bdcb-4965-b797-6ff115970374

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
import Theorems.Thm_TreeStack_MoveSignature_zero_count
import Theorems.Thm_TreeStack_MoveSignature_incoming_zero
import Theorems.Thm_TreeStack_MoveSignature_outgoing_zero
import Theorems.Thm_TreeStack_MoveSignature_extend_count_same
import Theorems.Thm_TreeStack_taskGainSum_toList
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_parent_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_carrier_erase_parent
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_parent
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_self
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_of_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_child_vertex
import Theorems.Thm_TreeStack_OrientedBranch_childMessageSum_eq_sum_term
import Theorems.Thm_TreeStack_OrientedBranch_childMessageTerm_eq_zero_of_not_occupiedChild
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_gain_eq_term
import Theorems.Thm_TreeStack_OrientedBranch_mem_occupiedChildTasks
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
attribute [local simp] TreeStack.OrientedBranch.root_mem_carrier
attribute [local simp] TreeStack.OrientedBranch.parent_mem_carrier
attribute [local simp] TreeStack.OrientedBranch.carrier_erase_parent
attribute [local simp] TreeStack.OrientedBranch.withBoundary_parent
attribute [local simp] TreeStack.OrientedBranch.withBoundary_self
attribute [local simp] TreeStack.OrientedBranch.withBoundary_of_mem_vertices
attribute [local simp] TreeStack.OrientedBranch.OccupiedChild.child_vertex
attribute [local simp] TreeStack.OrientedBranch.mem_occupiedChildTasks

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
variable [DecidableEq V]
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (B : OrientedBranch T) (C : Configuration V) :
    taskGainSum
        (fun t : B.OccupiedChild C => t.gain)
        (B.occupiedChildTasks C) =
      childMessageSum C B := by
  classical
  calc
    taskGainSum
        (fun t : B.OccupiedChild C => t.gain)
        (B.occupiedChildTasks C) =
        ∑ t : B.OccupiedChild C, t.gain := by
          rw [occupiedChildTasks, taskGainSum_toList]
    _ = ∑ t : B.OccupiedChild C,
          B.childMessageTerm C t.1 := by
          apply Finset.sum_congr rfl
          intro t _
          exact t.gain_eq_term
    _ = ∑ v ∈
          (Finset.univ.filter fun v : V =>
            B.IsOccupiedChildVertex C v),
          B.childMessageTerm C v := by
          symm
          simpa [OccupiedChild] using
            (Finset.sum_subtype
              (Finset.univ.filter fun v : V =>
                B.IsOccupiedChildVertex C v)
              (fun v => by simp)
              (fun v => B.childMessageTerm C v))
    _ = ∑ v : V, B.childMessageTerm C v := by
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro v hvUniv hvNot
          have hvNotOcc : ¬ B.IsOccupiedChildVertex C v := by
            intro hvOcc
            exact hvNot (Finset.mem_filter.mpr ⟨hvUniv, hvOcc⟩)
          exact B.childMessageTerm_eq_zero_of_not_occupiedChild C hvNotOcc
    _ = childMessageSum C B := (B.childMessageSum_eq_sum_term C).symm
end TreeStack.OrientedBranch
