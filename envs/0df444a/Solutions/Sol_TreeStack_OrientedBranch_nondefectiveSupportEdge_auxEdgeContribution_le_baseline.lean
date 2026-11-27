-- Prove2me | solution 1 for TreeStack.OrientedBranch.nondefectiveSupportEdge_auxEdgeContribution_le_baseline
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:25:50.292888+00:00
-- url     : https://prove2.me/submissions/adb90e90-f188-4634-913f-2d0db55080c8

import Mathlib
import Definitions.Def_TreeStack_Auxiliary
import Definitions.Def_TreeStack_AuxiliaryCharge
import Theorems.Thm_TreeStack_OrientedBranch_auxEdgeContribution_reverse
import Theorems.Thm_TreeStack_OrientedBranch_defectArrow_auxEdgeContribution_le_baseline_of_head_defect_zero
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
import Theorems.Thm_TreeStack_OrientedBranch_defect_equations_of_both_occupied
import Theorems.Thm_TreeStack_OrientedBranch_defectiveSupportEdge_reverse_iff
import Theorems.Thm_TreeStack_OrientedBranch_mem_occupiedChildTasks
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_empty
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_some
import Theorems.Thm_TreeStack_OrientedBranch_parent_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_root_ne_parent
import Theorems.Thm_TreeStack_OrientedBranch_supportEdge_defectArrow_or_reverse_or_both_neg
import Theorems.Thm_TreeStack_OrientedBranch_supportEdge_reverse_iff
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_of_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_parent
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_self
import Theorems.Thm_TreeStack_RootTask_branch_parent
import Theorems.Thm_TreeStack_RootTask_branch_root
import Theorems.Thm_TreeStack_defect_two_negative
import Theorems.Thm_TreeStack_empty_ne_integer_zero
import Theorems.Thm_TreeStack_incidentBranch_parent
import Theorems.Thm_TreeStack_incidentBranch_root
import Theorems.Thm_TreeStack_mass_oneOn
import Theorems.Thm_TreeStack_mem_rootTasks
import Theorems.Thm_TreeStack_mem_support_iff
import Theorems.Thm_TreeStack_oneOn_apply
import Theorems.Thm_TreeStack_scoreDefect_nonneg_iff
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
attribute [local simp] TreeStack.OrientedBranch.defectiveSupportEdge_reverse_iff
attribute [local simp] TreeStack.OrientedBranch.mem_occupiedChildTasks
attribute [local simp] TreeStack.OrientedBranch.messageContribution_empty
attribute [local simp] TreeStack.OrientedBranch.messageContribution_some
attribute [local simp] TreeStack.OrientedBranch.parent_mem_carrier
attribute [local simp] TreeStack.OrientedBranch.root_mem_carrier
attribute [local simp] TreeStack.OrientedBranch.root_mem_vertices
attribute [local simp] TreeStack.OrientedBranch.root_ne_parent
attribute [local simp] TreeStack.OrientedBranch.supportEdge_reverse_iff
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
attribute [local simp] TreeStack.scoreDefect_nonneg_iff


attribute [local simp] TreeStack.OrientedBranch.auxEdgeContribution_reverse

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T)
    (hEdge : B.SupportEdge C)
    (hNondef : ¬ B.DefectiveSupportEdge C) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent := by
  rcases B.supportEdge_defectArrow_or_reverse_or_both_neg C hEdge with
    hForward | hReverse | hBothNeg
  · have hDeltaZero : scoreDefect T C B.parent = 0 := by
      have hNonneg :=
        (scoreDefect_nonneg_iff T C B.parent).2 (hScores B.parent)
      by_contra hne
      have hPos : 0 < scoreDefect T C B.parent := by omega
      exact hNondef ⟨hEdge, Or.inl ⟨hForward.2, hPos⟩⟩
    exact
      defectArrow_auxEdgeContribution_le_baseline_of_head_defect_zero
        C ambientRoot hScores B hForward hDeltaZero
  · have hDeltaZero : scoreDefect T C B.root = 0 := by
      have hNonneg :=
        (scoreDefect_nonneg_iff T C B.root).2 (hScores B.root)
      by_contra hne
      have hPos : 0 < scoreDefect T C B.root := by omega
      exact hNondef ⟨hEdge, Or.inr (Or.inl ⟨hReverse.2, hPos⟩)⟩
    have h :=
      defectArrow_auxEdgeContribution_le_baseline_of_head_defect_zero
        C ambientRoot hScores B.reverseBranch hReverse (by simpa using hDeltaZero)
    simpa [add_comm] using h
  · have hRootZero : scoreDefect T C B.root = 0 := by
      have hNonneg :=
        (scoreDefect_nonneg_iff T C B.root).2 (hScores B.root)
      by_contra hne
      have hPos : 0 < scoreDefect T C B.root := by omega
      exact hNondef ⟨hEdge, Or.inr (Or.inr ⟨hBothNeg, Or.inl hPos⟩)⟩
    have hParentZero : scoreDefect T C B.parent = 0 := by
      have hNonneg :=
        (scoreDefect_nonneg_iff T C B.parent).2 (hScores B.parent)
      by_contra hne
      have hPos : 0 < scoreDefect T C B.parent := by omega
      exact hNondef ⟨hEdge, Or.inr (Or.inr ⟨hBothNeg, Or.inr hPos⟩)⟩
    have hEq :=
      B.defect_equations_of_both_occupied C hEdge.1 hEdge.2
    rcases
        defect_two_negative
          ((scoreDefect_nonneg_iff T C B.root).2 (hScores B.root))
          ((scoreDefect_nonneg_iff T C B.parent).2 (hScores B.parent))
          hEq.1 hEq.2 hBothNeg.1 hBothNeg.2 with
      ⟨r, q, hr, hq, ha, hb, hRoot, hParent⟩
    have hrZero : r = 0 := by omega
    have hqZero : q = 0 := by omega
    unfold auxEdgeContribution
    rw [ha, hb, hrZero, hqZero]
    ring_nf
    exact le_rfl
end TreeStack.OrientedBranch
