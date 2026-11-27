-- Prove2me | solution 1 for TreeStack.OrientedBranch.twoNegativeOwnerArrow_auxEdgeContribution_le_owner_charge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:23:41.346593+00:00
-- url     : https://prove2.me/submissions/d0bbafd5-7681-4498-977e-bd332f9cdbb1

import Mathlib
import Definitions.Def_TreeStack_Auxiliary
import Definitions.Def_TreeStack_AuxiliaryCharge
import Theorems.Thm_TreeStack_OrientedBranch_auxEdgeContribution_reverse
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
import Theorems.Thm_TreeStack_OrientedBranch_supportEdge_reverse_iff
import Theorems.Thm_TreeStack_OrientedBranch_two_mul_auxWeightInt_le_of_auxArrow
import Theorems.Thm_TreeStack_OrientedBranch_two_negative_parameters_toward_rootedOwner
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
import Theorems.Thm_TreeStack_two_negative_edge_excess_eq
import Theorems.Thm_TreeStack_two_negative_excess_le_owner_budget
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
    (hTwo : B.TwoNegativeOwnerArrow C ambientRoot) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent +
        auxWeightInt C ambientRoot hScores B.parent *
          scoreDefect T C B.parent := by
  have hAux :
      AuxArrow (T := T) C ambientRoot B.root B.parent := by
    refine ⟨B.adj, ?_⟩
    simpa only [incidentBranch_self] using
      (Or.inr hTwo :
        B.DefectArrow C ∨
          B.TwoNegativeOwnerArrow C ambientRoot)
  have hDouble :=
    two_mul_auxWeightInt_le_of_auxArrow
      C ambientRoot hScores hAux
  rcases
      B.two_negative_parameters_toward_rootedOwner
        C ambientRoot hTwo.1.1 hScores
        hTwo.2.1 hTwo.2.2.1 hTwo.2.2.2 with
    ⟨r, q, hr, hq, ha, hb, hRoot, hOwner⟩
  have hParent :
      scoreDefect T C B.parent = q + 2 * r := by
    rw [hTwo.2.2.2]
    exact hOwner
  have hEdge :=
    two_negative_edge_excess_eq
      (weightTail := auxWeightInt C ambientRoot hScores B.root)
      (weightHead := auxWeightInt C ambientRoot hScores B.parent)
      ha hb
  have hPay :=
    two_negative_excess_le_owner_budget
      (weightTail := auxWeightInt C ambientRoot hScores B.root)
      (weightOwner := auxWeightInt C ambientRoot hScores B.parent)
      (deltaOwner := scoreDefect T C B.parent)
      hq hDouble hParent
  unfold auxEdgeContribution
  linarith
end TreeStack.OrientedBranch
