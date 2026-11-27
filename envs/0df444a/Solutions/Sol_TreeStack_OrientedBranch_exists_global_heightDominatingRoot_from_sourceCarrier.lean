-- Prove2me | solution 1 for TreeStack.OrientedBranch.exists_global_heightDominatingRoot_from_sourceCarrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:37:05.442273+00:00
-- url     : https://prove2.me/submissions/358b254c-bf41-47ac-b53a-c62c7cb68c70

import Mathlib
import Definitions.Def_TreeStack_HeightSource
import Definitions.Def_TreeStack_Consolidation
import Theorems.Thm_TreeStack_OrientedBranch_mem_auxSourceFiber
import Theorems.Thm_TreeStack_OrientedBranch_auxSourceFiber_treePathConnected
import Theorems.Thm_TreeStack_OrientedBranch_treePathConnected_union_of_adj
import Theorems.Thm_TreeStack_OrientedBranch_exists_heightDominatingRoot_union_of_adj
import Theorems.Thm_TreeStack_OrientedBranch_exists_adj_mem_not_mem_of_nonempty_ne_univ
import Theorems.Thm_TreeStack_OrientedBranch_mem_auxSourceCarrier
import Theorems.Thm_TreeStack_OrientedBranch_auxSourceCarrier_insert
import Theorems.Thm_TreeStack_OrientedBranch_auxSourceCarrier_disjoint_fiber_of_not_mem
import Theorems.Thm_TreeStack_OrientedBranch_auxSourceFiber_heightDominated_of_nonempty
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


attribute [local simp] TreeStack.OrientedBranch.mem_auxSourceFiber
attribute [local simp] TreeStack.OrientedBranch.mem_auxSourceCarrier

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (R : Finset V) (r : V)
    (hConn :
      TreePathConnected (T := T)
        (auxSourceCarrier C ambientRoot hScores R))
    (hDom :
      HeightDominated (T := T)
        (fun v => auxHeight C ambientRoot hScores v)
        (auxSourceCarrier C ambientRoot hScores R) r) :
    ∃ t : V, ∀ v : V,
      auxHeight C ambientRoot hScores v ≤ T.graph.dist t v := by
  let S := auxSourceCarrier C ambientRoot hScores R
  by_cases hFull : S = (Finset.univ : Finset V)
  · refine ⟨r, ?_⟩
    intro v
    exact hDom.2 v (by simpa [S, hFull])
  · have hNonempty : S.Nonempty :=
      ⟨r, hDom.1⟩
    rcases
        exists_adj_mem_not_mem_of_nonempty_ne_univ
          (T := T) S hNonempty hFull with
      ⟨a, b, ha, hb, hadj⟩
    let s := auxSource C ambientRoot hScores b
    have hsNotR : s ∉ R := by
      intro hsR
      apply hb
      change b ∈ auxSourceCarrier C ambientRoot hScores R
      rw [mem_auxSourceCarrier]
      simpa [s] using hsR
    have hbFiber :
        b ∈ auxSourceFiber C ambientRoot hScores s := by
      simp [s]
    have hFiberNonempty :
        (auxSourceFiber C ambientRoot hScores s).Nonempty :=
      ⟨b, hbFiber⟩
    have hFiberConn :
        TreePathConnected (T := T)
          (auxSourceFiber C ambientRoot hScores s) :=
      auxSourceFiber_treePathConnected C ambientRoot hScores s
    have hFiberDom :
        HeightDominated (T := T)
          (fun v => auxHeight C ambientRoot hScores v)
          (auxSourceFiber C ambientRoot hScores s) s :=
      auxSourceFiber_heightDominated_of_nonempty
        C ambientRoot hScores s hFiberNonempty
    have hDisj :
        Disjoint S (auxSourceFiber C ambientRoot hScores s) := by
      simpa [S] using
        auxSourceCarrier_disjoint_fiber_of_not_mem
          C ambientRoot hScores R hsNotR
    have hMergedConn :
        TreePathConnected (T := T)
          (S ∪ auxSourceFiber C ambientRoot hScores s) :=
      treePathConnected_union_of_adj
        hConn hFiberConn ha hbFiber hadj
    rcases
        exists_heightDominatingRoot_union_of_adj
          (T := T)
          (fun v => auxHeight C ambientRoot hScores v)
          hConn hFiberConn hDisj ha hbFiber hadj hDom hFiberDom with
      ⟨t, hMergedDom⟩
    have hCarrierInsert :
        auxSourceCarrier C ambientRoot hScores (insert s R) =
          S ∪ auxSourceFiber C ambientRoot hScores s := by
      simpa [S] using
        auxSourceCarrier_insert C ambientRoot hScores R s
    have hConn' :
        TreePathConnected (T := T)
          (auxSourceCarrier C ambientRoot hScores (insert s R)) := by
      rw [hCarrierInsert]
      exact hMergedConn
    have hDom' :
        HeightDominated (T := T)
          (fun v => auxHeight C ambientRoot hScores v)
          (auxSourceCarrier C ambientRoot hScores (insert s R)) t := by
      rw [hCarrierInsert]
      exact hMergedDom
    exact
      solution
        C ambientRoot hScores (insert s R) t hConn' hDom'
termination_by ((Finset.univ : Finset V) \ R).card
decreasing_by
  have hsDiff : s ∈ ((Finset.univ : Finset V) \ R) := by
    simp [hsNotR]
  rw [Finset.sdiff_insert]
  exact Finset.card_erase_lt_of_mem hsDiff
end TreeStack.OrientedBranch
