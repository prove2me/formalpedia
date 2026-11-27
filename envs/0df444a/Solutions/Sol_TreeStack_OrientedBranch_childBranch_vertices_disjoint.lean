-- Prove2me | solution 1 for TreeStack.OrientedBranch.childBranch_vertices_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:35:48.787424+00:00
-- url     : https://prove2.me/submissions/ddc4c162-f6b7-47c9-ad04-fe39d8a6c021

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
import Theorems.Thm_TreeStack_MoveSignature_zero_count
import Theorems.Thm_TreeStack_MoveSignature_incoming_zero
import Theorems.Thm_TreeStack_MoveSignature_outgoing_zero
import Theorems.Thm_TreeStack_MoveSignature_extend_count_same
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_parent_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_carrier_erase_parent
import Theorems.Thm_TreeStack_F_three
import Theorems.Thm_TreeStack_F_two
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_root
import Theorems.Thm_TreeStack_OrientedBranch_edge_leaving_vertices_eq_boundary
import Theorems.Thm_TreeStack_OrientedBranch_eq_root_of_mem_vertices_adj_parent
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_empty
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_some
import Theorems.Thm_TreeStack_OrientedBranch_parent_not_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_root_ne_parent
import Theorems.Thm_TreeStack_empty_ne_integer_zero
import Theorems.Thm_TreeStack_mass_oneOn
import Theorems.Thm_TreeStack_mem_support_iff
import Theorems.Thm_TreeStack_oneOn_apply
attribute [local simp] TreeStack.F_three
attribute [local simp] TreeStack.F_two
attribute [local simp] TreeStack.OrientedBranch.childBranch_parent
attribute [local simp] TreeStack.OrientedBranch.childBranch_root
attribute [local simp] TreeStack.OrientedBranch.messageContribution_empty
attribute [local simp] TreeStack.OrientedBranch.messageContribution_some
attribute [local simp] TreeStack.OrientedBranch.root_mem_vertices
attribute [local simp] TreeStack.OrientedBranch.root_ne_parent
attribute [local simp] TreeStack.empty_ne_integer_zero
attribute [local simp] TreeStack.mass_oneOn
attribute [local simp] TreeStack.mem_support_iff
attribute [local simp] TreeStack.oneOn_apply


attribute [local simp] TreeStack.MoveSignature.zero_count
attribute [local simp] TreeStack.MoveSignature.incoming_zero
attribute [local simp] TreeStack.MoveSignature.outgoing_zero
attribute [local simp] TreeStack.MoveSignature.extend_count_same
attribute [local simp] TreeStack.OrientedBranch.root_mem_carrier
attribute [local simp] TreeStack.OrientedBranch.parent_mem_carrier
attribute [local simp] TreeStack.OrientedBranch.carrier_erase_parent

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (B : OrientedBranch T) (c d : B.Child)
    (hcd : c.vertex ≠ d.vertex) :
    Disjoint (B.childBranch c).vertices (B.childBranch d).vertices := by
  classical
  rw [Finset.disjoint_left]
  intro x hxc hxd
  have hdOutside : d.vertex ∉ (B.childBranch c).vertices := by
    intro hd
    have heq :=
      (B.childBranch c).eq_root_of_mem_vertices_adj_parent
        hd d.adj.symm
    exact hcd heq.symm
  have hdComp :
      d.vertex ∈ (B.childBranch d).component.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hxComp :
      x ∈ (B.childBranch d).component.supp := by
    simpa [vertices] using hxd
  have hreach :
      (B.childBranch d).deletedGraph.Reachable d.vertex x :=
    (B.childBranch d).component.reachable_of_mem_supp hdComp hxComp
  have hreach' :
      (T.graph.deleteEdges {s(d.vertex, B.root)}).Reachable d.vertex x := by
    simpa [deletedGraph, childBranch] using hreach
  rcases SimpleGraph.reachable_deleteEdges_iff_exists_walk.mp hreach' with
    ⟨p, havoidD⟩
  have hxcSet :
      x ∈ ((B.childBranch c).vertices : Set V) := by
    simpa using hxc
  have hdOutsideSet :
      d.vertex ∉ ((B.childBranch c).vertices : Set V) := by
    simpa using hdOutside
  rcases p.reverse.exists_boundary_dart
      ((B.childBranch c).vertices : Set V)
      hxcSet hdOutsideSet with
    ⟨⟨⟨u, v⟩, huv⟩, hdart, huSet, hvSet⟩
  have huFin : u ∈ (B.childBranch c).vertices := by
    simpa using huSet
  have hvFin : v ∉ (B.childBranch c).vertices := by
    simpa using hvSet
  have hedge :=
    (B.childBranch c).edge_leaving_vertices_eq_boundary
      huFin hvFin huv
  have hvRoot : v = B.root := by
    rw [Sym2.eq_iff] at hedge
    rcases hedge with h | h
    · simpa [childBranch] using h.2
    · have huParent : u = (B.childBranch c).parent := h.1
      subst u
      exact ((B.childBranch c).parent_not_mem_vertices huFin).elim
  have hrootRev : B.root ∈ p.reverse.support := by
    rw [← hvRoot]
    exact p.reverse.dart_snd_mem_support_of_mem_darts hdart
  have hroot : B.root ∈ p.support := by
    simpa using hrootRev
  let q : T.graph.Walk d.vertex B.root :=
    p.takeUntil B.root hroot
  have hqAvoid : s(d.vertex, B.root) ∉ q.edges := by
    intro hq
    exact havoidD (p.edges_takeUntil_subset_edges hroot hq)
  have hreachRoot :
      (T.graph.deleteEdges {s(d.vertex, B.root)}).Reachable
        d.vertex B.root :=
    SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr
      ⟨q, hqAvoid⟩
  have hbridge : T.graph.IsBridge s(d.vertex, B.root) :=
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp
      T.isTree.isAcyclic) d.adj.symm
  exact (SimpleGraph.isBridge_iff.mp hbridge) hreachRoot
end TreeStack.OrientedBranch
