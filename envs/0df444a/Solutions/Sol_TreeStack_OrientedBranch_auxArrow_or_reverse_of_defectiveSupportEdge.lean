-- Prove2me | solution 1 for TreeStack.OrientedBranch.auxArrow_or_reverse_of_defectiveSupportEdge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:10:04.36064+00:00
-- url     : https://prove2.me/submissions/c28f31e6-304e-413b-9d28-392b2e7032e3

import Mathlib
import Definitions.Def_TreeStack_DefectCharge
import Definitions.Def_TreeStack_Auxiliary
import Theorems.Thm_TreeStack_OrientedBranch_rootedOwner_eq_root_or_parent
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
import Theorems.Thm_TreeStack_OrientedBranch_defectiveSupportEdge_reverse_iff
import Theorems.Thm_TreeStack_OrientedBranch_mem_occupiedChildTasks
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_empty
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_some
import Theorems.Thm_TreeStack_OrientedBranch_parent_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_root_ne_parent
import Theorems.Thm_TreeStack_OrientedBranch_rootedOwner_reverse
import Theorems.Thm_TreeStack_OrientedBranch_supportEdge_defectArrow_or_reverse_or_both_neg
import Theorems.Thm_TreeStack_OrientedBranch_supportEdge_reverse_iff
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



set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (ambientRoot : V) (B : OrientedBranch T)
    (hDef : B.DefectiveSupportEdge C) :
    AuxArrow (T := T) C ambientRoot B.root B.parent ∨
      AuxArrow (T := T) C ambientRoot B.parent B.root := by
  rcases
      B.supportEdge_defectArrow_or_reverse_or_both_neg C hDef.1 with
    hForward | hReverse | hBothNeg
  · left
    refine ⟨B.adj, ?_⟩
    simpa using
      (Or.inl hForward :
        B.DefectArrow C ∨
          B.TwoNegativeOwnerArrow C ambientRoot)
  · right
    have hDefReverse :
        B.reverseBranch.DefectiveSupportEdge C :=
      (B.defectiveSupportEdge_reverse_iff C).2 hDef
    refine ⟨B.adj.symm, ?_⟩
    have hInc :
        incidentBranch T B.root B.parent B.adj.symm =
          B.reverseBranch := by
      exact incidentBranch_reverse_self B
    change
      (incidentBranch T B.root B.parent B.adj.symm).DefectArrow C ∨
        (incidentBranch T B.root B.parent B.adj.symm).TwoNegativeOwnerArrow
          C ambientRoot
    rw [hInc]
    exact Or.inl hReverse
  · rcases B.rootedOwner_eq_root_or_parent ambientRoot with
      hOwnerRoot | hOwnerParent
    · right
      have hDefReverse :
          B.reverseBranch.DefectiveSupportEdge C :=
        (B.defectiveSupportEdge_reverse_iff C).2 hDef
      have hOwnerReverse :
          B.reverseBranch.parent =
            B.reverseBranch.rootedOwner ambientRoot := by
        simpa [rootedOwner_reverse] using hOwnerRoot.symm
      have hTwoReverse :
          B.reverseBranch.TwoNegativeOwnerArrow C ambientRoot := by
        refine ⟨hDefReverse, hBothNeg.2, ?_, hOwnerReverse⟩
        simpa using hBothNeg.1
      refine ⟨B.adj.symm, ?_⟩
      have hInc :
          incidentBranch T B.root B.parent B.adj.symm =
            B.reverseBranch := by
        exact incidentBranch_reverse_self B
      change
        (incidentBranch T B.root B.parent B.adj.symm).DefectArrow C ∨
          (incidentBranch T B.root B.parent B.adj.symm).TwoNegativeOwnerArrow
            C ambientRoot
      rw [hInc]
      exact Or.inr hTwoReverse
    · left
      have hTwo :
          B.TwoNegativeOwnerArrow C ambientRoot :=
        ⟨hDef, hBothNeg.1, hBothNeg.2, hOwnerParent.symm⟩
      refine ⟨B.adj, ?_⟩
      simpa using
        (Or.inr hTwo :
          B.DefectArrow C ∨
            B.TwoNegativeOwnerArrow C ambientRoot)
end TreeStack.OrientedBranch
