-- Prove2me | solution 1 for TreeStack.taskGainSum_rootTasks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:54:53.28646+00:00
-- url     : https://prove2.me/submissions/1f2f855f-48db-40f4-852d-068cdb54769d

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
import Theorems.Thm_TreeStack_incidentBranch_root
import Theorems.Thm_TreeStack_incidentBranch_parent
import Theorems.Thm_TreeStack_RootTask_branch_root
import Theorems.Thm_TreeStack_RootTask_branch_parent
import Theorems.Thm_TreeStack_rootMessageTerm_eq_zero_of_not_occupied
import Theorems.Thm_TreeStack_RootTask_gain_eq_term
import Theorems.Thm_TreeStack_mem_rootTasks
import Theorems.Thm_TreeStack_F_three
import Theorems.Thm_TreeStack_F_two
import Theorems.Thm_TreeStack_MoveSignature_extend_count_same
import Theorems.Thm_TreeStack_MoveSignature_incoming_zero
import Theorems.Thm_TreeStack_MoveSignature_outgoing_zero
import Theorems.Thm_TreeStack_MoveSignature_zero_count
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_child_vertex
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_gain_eq_term
import Theorems.Thm_TreeStack_OrientedBranch_boundaryParityWeight_parent
import Theorems.Thm_TreeStack_OrientedBranch_carrier_erase_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_root
import Theorems.Thm_TreeStack_OrientedBranch_mem_occupiedChildTasks
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_empty
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_some
import Theorems.Thm_TreeStack_OrientedBranch_parent_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_root_ne_parent
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_of_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_parent
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_self
import Theorems.Thm_TreeStack_empty_ne_integer_zero
import Theorems.Thm_TreeStack_mass_oneOn
import Theorems.Thm_TreeStack_mem_support_iff
import Theorems.Thm_TreeStack_oneOn_apply
import Theorems.Thm_TreeStack_taskGainSum_toList
attribute [local simp] TreeStack.F_three
attribute [local simp] TreeStack.F_two
attribute [local simp] TreeStack.MoveSignature.extend_count_same
attribute [local simp] TreeStack.MoveSignature.incoming_zero
attribute [local simp] TreeStack.MoveSignature.outgoing_zero
attribute [local simp] TreeStack.MoveSignature.zero_count
attribute [local simp] TreeStack.OrientedBranch.OccupiedChild.child_vertex
attribute [local simp] TreeStack.OrientedBranch.boundaryParityWeight_parent
attribute [local simp] TreeStack.OrientedBranch.carrier_erase_parent
attribute [local simp] TreeStack.OrientedBranch.childBranch_parent
attribute [local simp] TreeStack.OrientedBranch.childBranch_root
attribute [local simp] TreeStack.OrientedBranch.mem_occupiedChildTasks
attribute [local simp] TreeStack.OrientedBranch.messageContribution_empty
attribute [local simp] TreeStack.OrientedBranch.messageContribution_some
attribute [local simp] TreeStack.OrientedBranch.parent_mem_carrier
attribute [local simp] TreeStack.OrientedBranch.root_mem_carrier
attribute [local simp] TreeStack.OrientedBranch.root_mem_vertices
attribute [local simp] TreeStack.OrientedBranch.root_ne_parent
attribute [local simp] TreeStack.OrientedBranch.withBoundary_of_mem_vertices
attribute [local simp] TreeStack.OrientedBranch.withBoundary_parent
attribute [local simp] TreeStack.OrientedBranch.withBoundary_self
attribute [local simp] TreeStack.empty_ne_integer_zero
attribute [local simp] TreeStack.mass_oneOn
attribute [local simp] TreeStack.mem_support_iff
attribute [local simp] TreeStack.oneOn_apply


attribute [local simp] TreeStack.incidentBranch_root
attribute [local simp] TreeStack.incidentBranch_parent
attribute [local simp] TreeStack.RootTask.branch_root
attribute [local simp] TreeStack.RootTask.branch_parent
attribute [local simp] TreeStack.mem_rootTasks

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
theorem _root_.solution
    (T : FiniteTree V) (C : Configuration V) (r : V) :
    taskGainSum
        (fun t : RootTask T C r => t.gain)
        (rootTasks T C r) =
      rootMessageSum T C r := by
  classical
  calc
    taskGainSum
        (fun t : RootTask T C r => t.gain)
        (rootTasks T C r) =
        ∑ t : RootTask T C r, t.gain := by
          rw [rootTasks, taskGainSum_toList]
    _ = ∑ t : RootTask T C r,
          rootMessageTerm T C r t.1 := by
          apply Finset.sum_congr rfl
          intro t _
          exact t.gain_eq_term
    _ = ∑ u ∈
          (Finset.univ.filter fun u : V =>
            IsOccupiedRootNeighbor T C r u),
          rootMessageTerm T C r u := by
          symm
          simpa [RootTask] using
            (Finset.sum_subtype
              (Finset.univ.filter fun u : V =>
                IsOccupiedRootNeighbor T C r u)
              (fun u => by simp)
              (fun u => rootMessageTerm T C r u))
    _ = ∑ u : V, rootMessageTerm T C r u := by
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro u huUniv huNot
          have huNotOcc : ¬ IsOccupiedRootNeighbor T C r u := by
            intro huOcc
            exact huNot (Finset.mem_filter.mpr ⟨huUniv, huOcc⟩)
          exact rootMessageTerm_eq_zero_of_not_occupied T C r huNotOcc
    _ = rootMessageSum T C r := rfl
end TreeStack
