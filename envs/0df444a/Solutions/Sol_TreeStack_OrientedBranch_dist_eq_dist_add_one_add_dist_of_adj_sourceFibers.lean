-- Prove2me | solution 1 for TreeStack.OrientedBranch.dist_eq_dist_add_one_add_dist_of_adj_sourceFibers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:34:57.087856+00:00
-- url     : https://prove2.me/submissions/acadd603-d0e5-410d-bea9-ae4e8511de9f

import Mathlib
import Definitions.Def_TreeStack_HeightSource
import Definitions.Def_TreeStack_Consolidation
import Theorems.Thm_TreeStack_OrientedBranch_mem_auxSourceFiber
import Theorems.Thm_TreeStack_OrientedBranch_auxSourceFiber_disjoint_of_ne
import Theorems.Thm_TreeStack_OrientedBranch_exists_path_within_auxSourceFiber
import Theorems.Thm_TreeStack_OrientedBranch_mem_auxSourceCarrier
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
import Theorems.Thm_TreeStack_OrientedBranch_tree_path_length_eq_dist
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
    {r s a b x y : V}
    (hrs : r ≠ s)
    (ha : a ∈ auxSourceFiber C ambientRoot hScores r)
    (hb : b ∈ auxSourceFiber C ambientRoot hScores s)
    (hadj : T.graph.Adj a b)
    (hx : x ∈ auxSourceFiber C ambientRoot hScores r)
    (hy : y ∈ auxSourceFiber C ambientRoot hScores s) :
    T.graph.dist x y =
      T.graph.dist x a + 1 + T.graph.dist b y := by
  rcases
      exists_path_within_auxSourceFiber
        C ambientRoot hScores r x a hx ha with
    ⟨px, hpxPath, hpxFiber⟩
  rcases
      exists_path_within_auxSourceFiber
        C ambientRoot hScores s b y hb hy with
    ⟨py, hpyPath, hpyFiber⟩
  have hFibDisj :=
    auxSourceFiber_disjoint_of_ne
      C ambientRoot hScores hrs
  have hbNotPx : b ∉ px.support := by
    intro hbpx
    have hbR := hpxFiber b hbpx
    exact (Finset.disjoint_left.mp hFibDisj) hbR hb
  let q : T.graph.Walk x b := px.concat hadj
  have hqPath : q.IsPath := by
    exact hpxPath.concat hbNotPx hadj
  have hbNotPyTail : b ∉ py.support.tail := by
    have hNodup := hpyPath.support_nodup
    rw [← py.cons_tail_support, List.nodup_cons] at hNodup
    exact hNodup.1
  have hDisjoint : q.support.Disjoint py.support.tail := by
    rw [List.disjoint_left]
    intro z hzq hzpyTail
    have hzpy : z ∈ py.support :=
      List.mem_of_mem_tail hzpyTail
    have hzS := hpyFiber z hzpy
    have hzq' :
        z ∈ px.support ∨ z = b := by
      simpa [q] using hzq
    rcases hzq' with hzpx | rfl
    · have hzR := hpxFiber z hzpx
      exact (Finset.disjoint_left.mp hFibDisj) hzR hzS
    · exact hbNotPyTail hzpyTail
  have hpPath : (q.append py).IsPath := by
    rw [SimpleGraph.Walk.isPath_def,
      SimpleGraph.Walk.support_append, List.nodup_append']
    exact
      ⟨hqPath.support_nodup, hpyPath.support_nodup.tail, hDisjoint⟩
  have hpxDist :=
    tree_path_length_eq_dist (T := T) px hpxPath
  have hpyDist :=
    tree_path_length_eq_dist (T := T) py hpyPath
  have hpDist :=
    tree_path_length_eq_dist (T := T) (q.append py) hpPath
  calc
    T.graph.dist x y = (q.append py).length := hpDist.symm
    _ = px.length + 1 + py.length := by
      simp [q]
    _ = T.graph.dist x a + 1 + T.graph.dist b y := by
      rw [hpxDist, hpyDist]
end TreeStack.OrientedBranch
