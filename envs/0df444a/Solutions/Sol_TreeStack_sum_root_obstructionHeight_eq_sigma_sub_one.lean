-- Prove2me | solution 1 for TreeStack.sum_root_obstructionHeight_eq_sigma_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:09:09.899564+00:00
-- url     : https://prove2.me/submissions/6714f7f9-6f30-45d9-87aa-3519dd1701ce

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
import Theorems.Thm_TreeStack_OrientedBranch_obstructionHeight_eq_one_add_two_mul_internalPotential
import Theorems.Thm_TreeStack_card_rootNeighbor
import Theorems.Thm_TreeStack_two_mul_sum_root_internalPotential
import Theorems.Thm_TreeStack_F_three
import Theorems.Thm_TreeStack_F_two
import Theorems.Thm_TreeStack_MoveSignature_extend_count_same
import Theorems.Thm_TreeStack_MoveSignature_incoming_zero
import Theorems.Thm_TreeStack_MoveSignature_outgoing_zero
import Theorems.Thm_TreeStack_MoveSignature_zero_count
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_child_vertex
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
import Theorems.Thm_TreeStack_RootTask_branch_parent
import Theorems.Thm_TreeStack_RootTask_branch_root
import Theorems.Thm_TreeStack_empty_ne_integer_zero
import Theorems.Thm_TreeStack_incidentBranch_parent
import Theorems.Thm_TreeStack_incidentBranch_root
import Theorems.Thm_TreeStack_mass_oneOn
import Theorems.Thm_TreeStack_mem_rootTasks
import Theorems.Thm_TreeStack_mem_support_iff
import Theorems.Thm_TreeStack_oneOn_apply
import Theorems.Thm_TreeStack_sigma_corrected_expansion
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
attribute [local simp] TreeStack.RootTask.branch_parent
attribute [local simp] TreeStack.RootTask.branch_root
attribute [local simp] TreeStack.empty_ne_integer_zero
attribute [local simp] TreeStack.incidentBranch_parent
attribute [local simp] TreeStack.incidentBranch_root
attribute [local simp] TreeStack.mass_oneOn
attribute [local simp] TreeStack.mem_rootTasks
attribute [local simp] TreeStack.mem_support_iff
attribute [local simp] TreeStack.oneOn_apply



set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
theorem _root_.solution
    (T : FiniteTree V) (r : V) :
    (∑ n : RootNeighbor T r, n.branch.obstructionHeight) =
      sigma T r - 1 := by
  classical
  have hHeights :
      (∑ n : RootNeighbor T r, n.branch.obstructionHeight) =
        Fintype.card (RootNeighbor T r) +
          2 * (∑ n : RootNeighbor T r, n.branch.internalPotential) := by
    calc
      (∑ n : RootNeighbor T r, n.branch.obstructionHeight) =
          ∑ n : RootNeighbor T r,
            (1 + 2 * n.branch.internalPotential) := by
              apply Finset.sum_congr rfl
              intro n _
              rw [OrientedBranch.obstructionHeight_eq_one_add_two_mul_internalPotential]
      _ = Fintype.card (RootNeighbor T r) +
          2 * (∑ n : RootNeighbor T r, n.branch.internalPotential) := by
            rw [Finset.sum_add_distrib]
            simp [← Finset.mul_sum]
  have hPotential :=
    two_mul_sum_root_internalPotential T r
  have hInternal :
      (∑ x ∈ (Finset.univ : Finset V).erase r,
        if 1 < T.graph.degree x then
          T.graph.degree x * 2 ^ T.graph.dist r x
        else
          0) =
        ∑ x ∈ nonRootInternalVertices T r,
          T.graph.degree x * 2 ^ T.graph.dist r x := by
    rw [← Finset.sum_filter]
    congr 1
    ext x
    simp [nonRootInternalVertices, and_left_comm, and_comm]
  rw [hHeights, card_rootNeighbor T r, hPotential, hInternal,
    sigma_corrected_expansion]
  omega
end TreeStack
