-- Prove2me | solution 1 for TreeStack.OrientedBranch.auxEdgeContribution_le_endpoint_add_separated_charges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:31:24.140482+00:00
-- url     : https://prove2.me/submissions/c39246c9-d11c-4a55-a1d6-01729dcdbb89

import Mathlib
import Definitions.Def_TreeStack_Auxiliary
import Definitions.Def_TreeStack_AuxiliaryCharge
import Theorems.Thm_TreeStack_OrientedBranch_auxEdgeContribution_reverse
import Theorems.Thm_TreeStack_OrientedBranch_supportEdge_auxEdgeContribution_le
import Theorems.Thm_TreeStack_OrientedBranch_auxEdgeContribution_eq_emptySide_charge
import Theorems.Thm_TreeStack_OrientedBranch_rootedOwner_eq_emptySide_of_root_pos
import Theorems.Thm_TreeStack_F_three
import Theorems.Thm_TreeStack_F_two
import Theorems.Thm_TreeStack_MoveSignature_extend_count_same
import Theorems.Thm_TreeStack_MoveSignature_incoming_zero
import Theorems.Thm_TreeStack_MoveSignature_outgoing_zero
import Theorems.Thm_TreeStack_MoveSignature_zero_count
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_child_vertex
import Theorems.Thm_TreeStack_OrientedBranch_auxWeightInt_nonneg
import Theorems.Thm_TreeStack_OrientedBranch_boundaryParityWeight_parent
import Theorems.Thm_TreeStack_OrientedBranch_carrier_erase_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_root
import Theorems.Thm_TreeStack_OrientedBranch_defectiveSupportEdge_reverse_iff
import Theorems.Thm_TreeStack_OrientedBranch_mem_occupiedChildTasks
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_empty
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_some
import Theorems.Thm_TreeStack_OrientedBranch_occupied_or_reverse_occupied
import Theorems.Thm_TreeStack_OrientedBranch_parent_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_root_ne_parent
import Theorems.Thm_TreeStack_OrientedBranch_rootedOwner_reverse
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


attribute [local simp] TreeStack.OrientedBranch.auxEdgeContribution_reverse

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (ambientRoot : V)
    (hRootPos : 0 < C ambientRoot)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent +
        retainedDefectCharge C ambientRoot hScores B +
        emptyBoundaryCharge C ambientRoot hScores B := by
  by_cases hEdge : B.SupportEdge C
  · have h :=
      supportEdge_auxEdgeContribution_le
        C ambientRoot hScores B hEdge
    simpa [retainedDefectCharge, emptyBoundaryCharge, hEdge, add_assoc] using h
  · have hNondef : ¬ B.DefectiveSupportEdge C := by
      intro hDef
      exact hEdge hDef.1
    have hOwnerBound :
        auxEdgeContribution C ambientRoot hScores B ≤
          auxWeightInt C ambientRoot hScores B.root +
            auxWeightInt C ambientRoot hScores B.parent +
            auxWeightInt C ambientRoot hScores (B.rootedOwner ambientRoot) *
              scoreDefect T C (B.rootedOwner ambientRoot) := by
      rcases B.occupied_or_reverse_occupied C hRootPos with hOcc | hRevOcc
      · have hEmpty : ¬ B.reverseBranch.Occupied C := by
          intro hRev
          exact hEdge ⟨hOcc, hRev⟩
        have hOwner :=
          rootedOwner_eq_emptySide_of_root_pos
            C ambientRoot B hRootPos hEmpty
        have hEq :=
          auxEdgeContribution_eq_emptySide_charge
            C ambientRoot hScores B hOcc hEmpty
        rw [hEq, hOwner]
        have hRootWeight :=
          auxWeightInt_nonneg C ambientRoot hScores B.root
        have hParentWeight :=
          auxWeightInt_nonneg C ambientRoot hScores B.parent
        linarith
      · have hEmpty : ¬ B.Occupied C := by
          intro hOcc
          exact hEdge ⟨hOcc, hRevOcc⟩
        have hOwner :=
          rootedOwner_eq_emptySide_of_root_pos
            C ambientRoot B.reverseBranch hRootPos hEmpty
        have hEq :=
          auxEdgeContribution_eq_emptySide_charge
            C ambientRoot hScores B.reverseBranch hRevOcc hEmpty
        have hOwner' : B.rootedOwner ambientRoot = B.root := by
          simpa [rootedOwner_reverse] using hOwner
        have hEq' :
            auxEdgeContribution C ambientRoot hScores B =
              auxWeightInt C ambientRoot hScores B.root *
                scoreDefect T C B.root := by
          simpa using hEq
        rw [hEq', hOwner']
        have hRootWeight :=
          auxWeightInt_nonneg C ambientRoot hScores B.root
        have hParentWeight :=
          auxWeightInt_nonneg C ambientRoot hScores B.parent
        linarith
    simpa [retainedDefectCharge, emptyBoundaryCharge, hEdge, hNondef,
      add_assoc] using hOwnerBound
end TreeStack.OrientedBranch
