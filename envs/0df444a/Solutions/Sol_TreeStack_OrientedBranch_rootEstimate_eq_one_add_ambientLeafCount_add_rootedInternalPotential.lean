-- Prove2me | solution 1 for TreeStack.OrientedBranch.rootEstimate_eq_one_add_ambientLeafCount_add_rootedInternalPotential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:29:44.93493+00:00
-- url     : https://prove2.me/submissions/af77bf1c-de6f-4064-91ed-10887fc6b34d

import Mathlib
import Definitions.Def_TreeStack_GlobalCharge
import Definitions.Def_TreeStack_LeafSlack
import Theorems.Thm_TreeStack_OrientedBranch_ambientLeaves_eq_insert_leafVertices_of_root_leaf
import Theorems.Thm_TreeStack_OrientedBranch_ambientLeaves_eq_leafVertices_of_root_not_leaf
import Theorems.Thm_TreeStack_OrientedBranch_ambientInternal_eq_nonRootInternal_of_root_not_internal
import Theorems.Thm_TreeStack_OrientedBranch_ambientInternal_eq_insert_nonRootInternal_of_root_internal
import Theorems.Thm_TreeStack_F_three
import Theorems.Thm_TreeStack_F_two
import Theorems.Thm_TreeStack_MoveSignature_extend_count_same
import Theorems.Thm_TreeStack_MoveSignature_incoming_zero
import Theorems.Thm_TreeStack_MoveSignature_outgoing_zero
import Theorems.Thm_TreeStack_MoveSignature_zero_count
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_child_vertex
import Theorems.Thm_TreeStack_OrientedBranch_auxEdgeContribution_reverse
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
import Theorems.Thm_TreeStack_rootEstimate_corrected_expansion
import Theorems.Thm_TreeStack_scoreDefect_nonneg_iff
attribute [local simp] TreeStack.F_three
attribute [local simp] TreeStack.F_two
attribute [local simp] TreeStack.MoveSignature.extend_count_same
attribute [local simp] TreeStack.MoveSignature.incoming_zero
attribute [local simp] TreeStack.MoveSignature.outgoing_zero
attribute [local simp] TreeStack.MoveSignature.zero_count
attribute [local simp] TreeStack.OrientedBranch.OccupiedChild.child_vertex
attribute [local simp] TreeStack.OrientedBranch.auxEdgeContribution_reverse
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
    [Nontrivial V] (T : FiniteTree V) (r : V) :
    rootEstimate T r =
      1 + ambientLeafCount (T := T) + rootedInternalPotential T r := by
  classical
  have hdeg :
      0 < T.graph.degree r :=
    T.isTree.connected.preconnected.degree_pos_of_nontrivial r
  by_cases hLeaf : T.graph.degree r = 1
  · have hLeaves :=
      ambientLeaves_eq_insert_leafVertices_of_root_leaf T r hLeaf
    have hrNotLeaf : r ∉ leafVertices T r := by
      simp [leafVertices]
    have hLeafCount :
        ambientLeafCount (T := T) = leafCount T r + 1 := by
      unfold ambientLeafCount leafCount
      rw [hLeaves]
      simp [hrNotLeaf]
    have hNotInternal : ¬ 1 < T.graph.degree r := by
      omega
    have hInternal :=
      ambientInternal_eq_nonRootInternal_of_root_not_internal
        T r hNotInternal
    have hPotential :
        rootedInternalPotential T r =
          ∑ v ∈ nonRootInternalVertices T r,
            T.graph.degree v * 2 ^ T.graph.dist r v := by
      unfold rootedInternalPotential
      rw [hInternal]
    rw [rootEstimate_corrected_expansion, hLeafCount, hPotential, hLeaf]
    omega
  · have hInternalRoot : 1 < T.graph.degree r := by
      omega
    have hLeaves :=
      ambientLeaves_eq_leafVertices_of_root_not_leaf T r hLeaf
    have hLeafCount :
        ambientLeafCount (T := T) = leafCount T r := by
      unfold ambientLeafCount leafCount
      rw [hLeaves]
    have hInternal :=
      ambientInternal_eq_insert_nonRootInternal_of_root_internal
        T r hInternalRoot
    have hrNotInternal : r ∉ nonRootInternalVertices T r := by
      simp [nonRootInternalVertices]
    have hPotential :
        rootedInternalPotential T r =
          T.graph.degree r +
            ∑ v ∈ nonRootInternalVertices T r,
              T.graph.degree v * 2 ^ T.graph.dist r v := by
      unfold rootedInternalPotential
      rw [hInternal, Finset.sum_insert hrNotInternal]
      simp
    rw [rootEstimate_corrected_expansion, hLeafCount, hPotential]
    omega
end TreeStack.OrientedBranch
