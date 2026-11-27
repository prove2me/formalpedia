-- Prove2me | solution 1 for TreeStack.obstruction_score_selected_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:10:18.729415+00:00
-- url     : https://prove2.me/submissions/44a8c659-0c04-460c-a8e9-f52f69f3a610

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
import Theorems.Thm_TreeStack_OrientedBranch_obstruction_branchMessage
import Theorems.Thm_TreeStack_sum_dite_rootNeighbors
import Theorems.Thm_TreeStack_sum_root_obstructionHeight_eq_sigma_sub_one
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
import Theorems.Thm_TreeStack_OrientedBranch_parent_not_mem_vertices
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
    score T (obstruction T r) r = 0 := by
  classical
  have hTerms :
      rootMessageSum T (obstruction T r) r =
        -((sigma T r - 1 : ℕ) : ℤ) := by
    rw [rootMessageSum]
    calc
      (∑ u : V, rootMessageTerm T (obstruction T r) r u) =
          ∑ u : V,
            if h : T.graph.Adj u r then
              -((incidentBranch T r u h).obstructionHeight : ℤ)
            else
              0 := by
                apply Finset.sum_congr rfl
                intro u _
                by_cases h : T.graph.Adj u r
                · let B : OrientedBranch T := incidentBranch T r u h
                  have hAway : r ∉ B.vertices := by
                    simpa [B, incidentBranch] using B.parent_not_mem_vertices
                  have hMsg :=
                    (B.obstruction_branchMessage r hAway).2
                  simp [rootMessageTerm, h, B, hMsg]
                · simp [rootMessageTerm, h]
      _ = ∑ n : RootNeighbor T r,
            -((n.branch.obstructionHeight : ℕ) : ℤ) := by
              exact
                sum_dite_rootNeighbors T r
                  (fun n : RootNeighbor T r =>
                    -((n.branch.obstructionHeight : ℕ) : ℤ))
      _ = -((∑ n : RootNeighbor T r,
            n.branch.obstructionHeight : ℕ) : ℤ) := by
              push_cast
              rw [Finset.sum_neg_distrib]
      _ = -((sigma T r - 1 : ℕ) : ℤ) := by
              rw [sum_root_obstructionHeight_eq_sigma_sub_one]
  rw [score, obstruction_root, hTerms]
  ring
end TreeStack
