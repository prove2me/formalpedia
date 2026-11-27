-- Prove2me | solution 1 for TreeStack.OrientedBranch.obstruction_branchMessage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:59:11.586795+00:00
-- url     : https://prove2.me/submissions/6cc657c3-833e-4cc4-a706-bd934221417f

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
import Theorems.Thm_TreeStack_obstruction_leaf
import Theorems.Thm_TreeStack_obstruction_internal
import Theorems.Thm_TreeStack_OrientedBranch_obstructionHeight_leaf
import Theorems.Thm_TreeStack_OrientedBranch_obstructionHeight_internal
import Theorems.Thm_TreeStack_OrientedBranch_no_child_of_degree_one
import Theorems.Thm_TreeStack_OrientedBranch_child_nonempty_of_internal
import Theorems.Thm_TreeStack_F_of_le_one
import Theorems.Thm_TreeStack_F_three
import Theorems.Thm_TreeStack_F_two
import Theorems.Thm_TreeStack_MoveSignature_extend_count_same
import Theorems.Thm_TreeStack_MoveSignature_incoming_zero
import Theorems.Thm_TreeStack_MoveSignature_outgoing_zero
import Theorems.Thm_TreeStack_MoveSignature_zero_count
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_child_vertex
import Theorems.Thm_TreeStack_OrientedBranch_boundaryParityWeight_parent
import Theorems.Thm_TreeStack_OrientedBranch_branchMessage_eq_some_of_occupied
import Theorems.Thm_TreeStack_OrientedBranch_carrier_erase_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_card_lt
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_root
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_vertices_subset
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
open TreeStack.OrientedBranch
namespace TreeStack.OrientedBranch
theorem _root_.solution (r : V) (B : OrientedBranch T)
    (hAway : r ∉ B.vertices) :
    B.Occupied (obstruction T r) ∧
      branchMessage (obstruction T r) B =
        some (-(B.obstructionHeight : ℤ)) := by
  classical
  have hRootNe : B.root ≠ r := by
    intro h
    subst r
    exact hAway B.root_mem_vertices
  by_cases hLeaf : T.graph.degree B.root = 1
  · have hRoot :
        obstruction T r B.root = 1 :=
      obstruction_leaf T r B.root hRootNe hLeaf
    have hOcc : B.Occupied (obstruction T r) := by
      refine ⟨B.root, B.root_mem_vertices, ?_⟩
      rw [hRoot]
      omega
    refine ⟨hOcc, ?_⟩
    rw [branchMessage_eq_some_of_occupied _ _ hOcc]
    have hEff :
        effectiveInput (obstruction T r) B = 1 := by
      rw [effectiveInput, childMessageSum]
      simp [hRoot, B.no_child_of_degree_one hLeaf]
    rw [hEff, B.obstructionHeight_leaf hLeaf]
    norm_num [F]
  · have hPos : 0 < T.graph.degree B.root := by
      rw [T.graph.degree_pos_iff_exists_adj B.root]
      exact ⟨B.parent, B.adj⟩
    have hInternal : 1 < T.graph.degree B.root := by
      omega
    have hRoot :
        obstruction T r B.root = 0 :=
      obstruction_internal T r B.root hRootNe hLeaf
    let H : ℕ :=
      ∑ v : V,
        if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
          obstructionHeight
            (B.childBranch
              { vertex := v
                adj := h.1
                ne_parent := h.2 })
        else
          0
    have hChildSum :
        childMessageSum (obstruction T r) B = -(H : ℤ) := by
      rw [childMessageSum]
      dsimp [H]
      push_cast
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro v _
      by_cases h : T.graph.Adj B.root v ∧ v ≠ B.parent
      · let c : B.Child :=
          { vertex := v
            adj := h.1
            ne_parent := h.2 }
        have hAwayChild :
            r ∉ (B.childBranch c).vertices := by
          intro hr
          exact hAway (B.childBranch_vertices_subset c hr)
        have hRec :=
          solution r (B.childBranch c) hAwayChild
        simp [h, c, hRec.2]
      · simp [h]
    have hOcc : B.Occupied (obstruction T r) := by
      let c : B.Child := Classical.choice (B.child_nonempty_of_internal hInternal)
      have hAwayChild :
          r ∉ (B.childBranch c).vertices := by
        intro hr
        exact hAway (B.childBranch_vertices_subset c hr)
      have hRec :=
        solution r (B.childBranch c) hAwayChild
      rcases hRec.1 with ⟨w, hw, hpos⟩
      exact ⟨w, B.childBranch_vertices_subset c hw, hpos⟩
    refine ⟨hOcc, ?_⟩
    rw [branchMessage_eq_some_of_occupied _ _ hOcc]
    have hEff :
        effectiveInput (obstruction T r) B = -(H : ℤ) := by
      rw [effectiveInput, hRoot, hChildSum]
      simp
    rw [hEff]
    have hle : -(H : ℤ) ≤ 1 := by omega
    rw [F_of_le_one hle, B.obstructionHeight_internal hInternal]
    dsimp [H]
    push_cast
    ring_nf
termination_by B.card
decreasing_by
  all_goals
    exact B.childBranch_card_lt _
end TreeStack.OrientedBranch
