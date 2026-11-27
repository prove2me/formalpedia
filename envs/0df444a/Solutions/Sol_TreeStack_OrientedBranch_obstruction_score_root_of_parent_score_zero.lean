-- Prove2me | solution 1 for TreeStack.OrientedBranch.obstruction_score_root_of_parent_score_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:00:22.266327+00:00
-- url     : https://prove2.me/submissions/5dfb60b6-d3d3-455d-8195-36c791e8af3f

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
import Theorems.Thm_TreeStack_OrientedBranch_obstructionHeight_leaf
import Theorems.Thm_TreeStack_OrientedBranch_obstructionHeight_internal
import Theorems.Thm_TreeStack_OrientedBranch_obstructionHeight_pos
import Theorems.Thm_TreeStack_OrientedBranch_obstruction_branchMessage
import Theorems.Thm_TreeStack_OrientedBranch_score_eq_effectiveInput_add_reverse
import Theorems.Thm_TreeStack_OrientedBranch_effectiveInput_eq_zero_of_not_occupied
import Theorems.Thm_TreeStack_F_eq_neg_odd_iff
import Theorems.Thm_TreeStack_F_eq_nonneg_iff
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
    (r : V) (B : OrientedBranch T)
    (hAway : r ∉ B.vertices)
    (hParent :
      score T (obstruction T r) B.parent = 0) :
    score T (obstruction T r) B.root = 0 := by
  classical
  let C : Configuration V := obstruction T r
  let R : OrientedBranch T := B.reverseBranch
  have hData := obstruction_branchMessage r B hAway
  have hOccB : B.Occupied C := by
    simpa [C] using hData.1
  have hMsgB :
      branchMessage C B =
        some (-(B.obstructionHeight : ℤ)) := by
    simpa [C] using hData.2
  have hFEff :
      F (B.effectiveInput C) =
        -(B.obstructionHeight : ℤ) := by
    have hDef :=
      branchMessage_eq_some_of_occupied C B hOccB
    rw [hMsgB] at hDef
    exact Option.some.inj hDef.symm
  have hParentDecomp :
      score T C B.parent =
        R.effectiveInput C +
          messageContribution (branchMessage C R.reverseBranch) := by
    simpa [R] using score_eq_effectiveInput_add_reverse C R
  have hRevRev : R.reverseBranch = B := by
    simp [R]
  have hParentC : score T C B.parent = 0 := by
    simpa [C] using hParent
  have hEffR :
      R.effectiveInput C = (B.obstructionHeight : ℤ) := by
    rw [hParentC, hRevRev, hMsgB] at hParentDecomp
    simp only [messageContribution_some] at hParentDecomp
    linarith
  have hOccR : R.Occupied C := by
    by_contra hEmpty
    have hZero :=
      effectiveInput_eq_zero_of_not_occupied C R hEmpty
    rw [hZero] at hEffR
    have hPos : 0 < (B.obstructionHeight : ℤ) := by
      exact_mod_cast B.obstructionHeight_pos
    linarith
  have hMsgR :
      branchMessage C R =
        some (F (B.obstructionHeight : ℤ)) := by
    rw [branchMessage_eq_some_of_occupied C R hOccR, hEffR]
  have hRootDecomp :=
    score_eq_effectiveInput_add_reverse C B
  change
    score T C B.root =
      B.effectiveInput C +
        messageContribution (branchMessage C R) at hRootDecomp
  rw [hMsgR] at hRootDecomp
  simp only [messageContribution_some] at hRootDecomp
  by_cases hLeaf : T.graph.degree B.root = 1
  · have hHeight : B.obstructionHeight = 1 :=
      B.obstructionHeight_leaf hLeaf
    have hFEff' :
        F (B.effectiveInput C) = -(2 * (0 : ℤ) + 1) := by
      simpa [hHeight] using hFEff
    have hInput :
        B.effectiveInput C = 1 := by
      exact
        (F_eq_neg_odd_iff (z := B.effectiveInput C) (r := (0 : ℤ))
          (by omega)).1 hFEff'
    rw [hHeight] at hRootDecomp
    norm_num [F] at hRootDecomp
    linarith
  · have hPosDegree : 0 < T.graph.degree B.root := by
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
    have hHeight :
        B.obstructionHeight = 3 + 2 * H := by
      simpa [H] using B.obstructionHeight_internal hInternal
    have hFEff' :
        F (B.effectiveInput C) =
          -(2 * ((H : ℤ) + 1) + 1) := by
      rw [hHeight] at hFEff
      push_cast at hFEff
      linarith
    have hInput :
        B.effectiveInput C = -(H : ℤ) := by
      have hInv :=
        (F_eq_neg_odd_iff
          (z := B.effectiveInput C)
          (r := (H : ℤ) + 1) (by positivity)).1 hFEff'
      linarith
    have hFHeight :
        F (B.obstructionHeight : ℤ) = (H : ℤ) := by
      apply
        (F_eq_nonneg_iff
          (z := (B.obstructionHeight : ℤ))
          (k := (H : ℤ)) (by positivity)).2
      right
      rw [hHeight]
      push_cast
      ring
    rw [hFHeight, hInput] at hRootDecomp
    linarith
end TreeStack.OrientedBranch
