-- Prove2me | solution 1 for TreeStack.OrientedBranch.obstructionHeight_eq_one_add_two_mul_internalPotential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:04:56.09503+00:00
-- url     : https://prove2.me/submissions/d0daea0a-feab-4dd1-9328-9be6e4288fee

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
import Theorems.Thm_TreeStack_OrientedBranch_obstructionHeight_leaf
import Theorems.Thm_TreeStack_OrientedBranch_obstructionHeight_internal
import Theorems.Thm_TreeStack_OrientedBranch_vertices_eq_singleton_of_degree_one
import Theorems.Thm_TreeStack_OrientedBranch_sum_dite_children
import Theorems.Thm_TreeStack_OrientedBranch_card_childFinset_add_one
import Theorems.Thm_TreeStack_OrientedBranch_two_mul_sum_child_internalPotential
import Theorems.Thm_TreeStack_F_three
import Theorems.Thm_TreeStack_F_two
import Theorems.Thm_TreeStack_MoveSignature_extend_count_same
import Theorems.Thm_TreeStack_MoveSignature_incoming_zero
import Theorems.Thm_TreeStack_MoveSignature_outgoing_zero
import Theorems.Thm_TreeStack_MoveSignature_zero_count
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_child_vertex
import Theorems.Thm_TreeStack_OrientedBranch_boundaryParityWeight_parent
import Theorems.Thm_TreeStack_OrientedBranch_carrier_erase_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_card_lt
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
theorem _root_.solution
    (B : OrientedBranch T) :
    B.obstructionHeight = 1 + 2 * B.internalPotential := by
  classical
  by_cases hLeaf : T.graph.degree B.root = 1
  · rw [B.obstructionHeight_leaf hLeaf, internalPotential,
      B.vertices_eq_singleton_of_degree_one hLeaf]
    simp [hLeaf]
  · have hPos : 0 < T.graph.degree B.root := by
      rw [T.graph.degree_pos_iff_exists_adj B.root]
      exact ⟨B.parent, B.adj⟩
    have hInternal : 1 < T.graph.degree B.root := by
      omega
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
    let P : ℕ :=
      ∑ c : B.Child, (B.childBranch c).internalPotential
    have hRec :
        H =
          ∑ v : V,
            if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
              1 + 2 *
                (B.childBranch
                  { vertex := v
                    adj := h.1
                    ne_parent := h.2 }).internalPotential
            else
              0 := by
      dsimp [H]
      apply Finset.sum_congr rfl
      intro v _
      by_cases h : T.graph.Adj B.root v ∧ v ≠ B.parent
      · simp [h,
          solution
            (B.childBranch
              { vertex := v
                adj := h.1
                ne_parent := h.2 })]
      · simp [h]
    have hCount :
        (∑ v : V,
          if T.graph.Adj B.root v ∧ v ≠ B.parent then
            (1 : ℕ)
          else
            0) =
          B.childFinset.card := by
      calc
        (∑ v : V,
          if T.graph.Adj B.root v ∧ v ≠ B.parent then
            (1 : ℕ)
          else
            0) =
            ((Finset.univ : Finset V).filter
              (fun v => T.graph.Adj B.root v ∧ v ≠ B.parent)).card := by
                simpa using
                  (Finset.sum_boole (R := ℕ)
                    (fun v : V =>
                      T.graph.Adj B.root v ∧ v ≠ B.parent)
                    (Finset.univ : Finset V))
        _ = B.childFinset.card := by
              congr 1
              ext v
              simp [childFinset, and_left_comm, and_comm]
    have hPSum :
        (∑ v : V,
          if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
            (B.childBranch
              { vertex := v
                adj := h.1
                ne_parent := h.2 }).internalPotential
          else
            0) = P := by
      dsimp [P]
      exact
        B.sum_dite_children
          (fun c : B.Child => (B.childBranch c).internalPotential)
    have hH :
        H = B.childFinset.card + 2 * P := by
      rw [hRec]
      calc
        (∑ v : V,
          if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
            1 + 2 *
              (B.childBranch
                { vertex := v
                  adj := h.1
                  ne_parent := h.2 }).internalPotential
          else
            0) =
            (∑ v : V,
              if T.graph.Adj B.root v ∧ v ≠ B.parent then
                (1 : ℕ)
              else
                0) +
              2 *
                (∑ v : V,
                  if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
                    (B.childBranch
                      { vertex := v
                        adj := h.1
                        ne_parent := h.2 }).internalPotential
                  else
                    0) := by
                      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
                      apply Finset.sum_congr rfl
                      intro v _
                      by_cases h :
                          T.graph.Adj B.root v ∧ v ≠ B.parent
                      · simp [h]
                      · simp [h]
        _ = B.childFinset.card + 2 * P := by
              rw [hCount, hPSum]
    let Q : ℕ :=
      ∑ x ∈ B.vertices.erase B.root,
        if 1 < T.graph.degree x then
          T.graph.degree x * 2 ^ T.graph.dist B.root x
        else
          0
    have hQ : 2 * P = Q := by
      dsimp [P, Q]
      exact B.two_mul_sum_child_internalPotential
    have hPot :
        B.internalPotential = Q + T.graph.degree B.root := by
      let weight : V → ℕ := fun x =>
        if 1 < T.graph.degree x then
          T.graph.degree x * 2 ^ T.graph.dist B.root x
        else
          0
      rw [internalPotential]
      change
        (∑ x ∈ B.vertices, weight x) =
          Q + T.graph.degree B.root
      calc
        (∑ x ∈ B.vertices, weight x) =
            (∑ x ∈ B.vertices.erase B.root, weight x) +
              weight B.root := by
                symm
                exact
                  Finset.sum_erase_add B.vertices weight
                    B.root_mem_vertices
        _ = Q + T.graph.degree B.root := by
              dsimp [Q, weight]
              simp [hInternal]
    rw [B.obstructionHeight_internal hInternal]
    change 3 + 2 * H = 1 + 2 * B.internalPotential
    have hCard := B.card_childFinset_add_one
    omega
termination_by B.card
decreasing_by
  all_goals
    exact B.childBranch_card_lt _
end TreeStack.OrientedBranch
