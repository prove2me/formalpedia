-- Prove2me | solution 1 for TreeStack.incidentBranch_vertices_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:41:26.439623+00:00
-- url     : https://prove2.me/submissions/11731bb0-9071-45a8-95ec-6c38fd3f0469

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
import Theorems.Thm_TreeStack_incidentBranch_root
import Theorems.Thm_TreeStack_incidentBranch_parent
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
import Theorems.Thm_TreeStack_OrientedBranch_edge_leaving_vertices_eq_boundary
import Theorems.Thm_TreeStack_OrientedBranch_eq_root_of_mem_vertices_adj_parent
import Theorems.Thm_TreeStack_OrientedBranch_mem_occupiedChildTasks
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_empty
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_some
import Theorems.Thm_TreeStack_OrientedBranch_parent_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_parent_not_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_root_ne_parent
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_of_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_parent
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_self
import Theorems.Thm_TreeStack_empty_ne_integer_zero
import Theorems.Thm_TreeStack_mass_oneOn
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
attribute [local simp] TreeStack.empty_ne_integer_zero
attribute [local simp] TreeStack.mass_oneOn
attribute [local simp] TreeStack.mem_support_iff
attribute [local simp] TreeStack.oneOn_apply


attribute [local simp] TreeStack.incidentBranch_root
attribute [local simp] TreeStack.incidentBranch_parent

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
theorem _root_.solution
    (r : V) {u v : V}
    (hu : T.graph.Adj u r) (hv : T.graph.Adj v r)
    (huv : u ≠ v) :
    Disjoint
      (incidentBranch T r u hu).vertices
      (incidentBranch T r v hv).vertices := by
  classical
  let A : OrientedBranch T := incidentBranch T r u hu
  let B : OrientedBranch T := incidentBranch T r v hv
  rw [Finset.disjoint_left]
  intro x hxA hxB
  have hvOutside : v ∉ A.vertices := by
    intro hvA
    have heq :=
      A.eq_root_of_mem_vertices_adj_parent
        hvA (by simpa [A, incidentBranch] using hv)
    have heq' : v = u := by
      simpa [A, incidentBranch] using heq
    exact huv heq'.symm
  have hvComp0 : B.root ∈ B.component.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hvComp : v ∈ B.component.supp := by
    simpa [B, incidentBranch] using hvComp0
  have hxComp : x ∈ B.component.supp := by
    simpa [OrientedBranch.vertices] using hxB
  have hreach : B.deletedGraph.Reachable v x := by
    have :=
      B.component.reachable_of_mem_supp hvComp hxComp
    simpa [B, incidentBranch] using this
  have hreach' :
      (T.graph.deleteEdges {s(v, r)}).Reachable v x := by
    simpa [B, incidentBranch, OrientedBranch.deletedGraph] using hreach
  rcases SimpleGraph.reachable_deleteEdges_iff_exists_walk.mp hreach' with
    ⟨p, havoidB⟩
  have hxASet : x ∈ (A.vertices : Set V) := by
    simpa using hxA
  have hvOutsideSet : v ∉ (A.vertices : Set V) := by
    simpa using hvOutside
  rcases p.reverse.exists_boundary_dart
      (A.vertices : Set V) hxASet hvOutsideSet with
    ⟨⟨⟨a, b⟩, hab⟩, hdart, haSet, hbSet⟩
  have haFin : a ∈ A.vertices := by simpa using haSet
  have hbFin : b ∉ A.vertices := by simpa using hbSet
  have hedge :=
    A.edge_leaving_vertices_eq_boundary haFin hbFin hab
  have hbRoot : b = r := by
    rw [Sym2.eq_iff] at hedge
    rcases hedge with h | h
    · have : b = A.parent := h.2
      simpa [A, incidentBranch] using this
    · have haParent : a = A.parent := h.1
      have : a = r := by simpa [A, incidentBranch] using haParent
      subst a
      have hrNot : r ∉ A.vertices := by
        simpa [A, incidentBranch] using A.parent_not_mem_vertices
      exact (hrNot haFin).elim
  have hrRev : r ∈ p.reverse.support := by
    rw [← hbRoot]
    exact p.reverse.dart_snd_mem_support_of_mem_darts hdart
  have hr : r ∈ p.support := by simpa using hrRev
  let q : T.graph.Walk v r := p.takeUntil r hr
  have hqAvoid : s(v, r) ∉ q.edges := by
    intro hq
    exact havoidB (p.edges_takeUntil_subset_edges hr hq)
  have hreachRoot :
      (T.graph.deleteEdges {s(v, r)}).Reachable v r :=
    SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr
      ⟨q, hqAvoid⟩
  have hbridge : T.graph.IsBridge s(v, r) :=
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp
      T.isTree.isAcyclic) hv
  exact (SimpleGraph.isBridge_iff.mp hbridge) hreachRoot
end TreeStack
