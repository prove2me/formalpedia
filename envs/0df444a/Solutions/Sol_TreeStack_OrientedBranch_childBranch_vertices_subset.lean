-- Prove2me | solution 1 for TreeStack.OrientedBranch.childBranch_vertices_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:13:17.7185+00:00
-- url     : https://prove2.me/submissions/93bb6b9f-3ef0-40fa-a2b6-3be7be35c3a3

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch
import Theorems.Thm_TreeStack_OrientedBranch_root_ne_parent
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_root
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_parent
import Theorems.Thm_TreeStack_OrientedBranch_childEdge_ne_boundary
import Theorems.Thm_TreeStack_mem_support_iff
attribute [local simp] TreeStack.mem_support_iff


attribute [local simp] TreeStack.OrientedBranch.root_ne_parent
attribute [local simp] TreeStack.OrientedBranch.root_mem_vertices
attribute [local simp] TreeStack.OrientedBranch.childBranch_root
attribute [local simp] TreeStack.OrientedBranch.childBranch_parent

set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution (B : OrientedBranch T) (c : B.Child) :
    (B.childBranch c).vertices ⊆ B.vertices := by
  classical
  intro x hx
  rw [vertices, Set.mem_toFinset] at hx ⊢
  have hc :
      c.vertex ∈ (B.childBranch c).component.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hreachChild :
      (B.childBranch c).deletedGraph.Reachable c.vertex x :=
    (B.childBranch c).component.reachable_of_mem_supp hc hx
  have hreachChild' :
      (T.graph.deleteEdges {s(c.vertex, B.root)}).Reachable c.vertex x := by
    simpa [deletedGraph, childBranch] using hreachChild
  rcases SimpleGraph.reachable_deleteEdges_iff_exists_walk.mp hreachChild' with
    ⟨p, hchildEdge⟩
  have hparentEdge : s(B.root, B.parent) ∉ p.edges := by
    intro hp
    have hrootSupp : B.root ∈ p.support :=
      p.fst_mem_support_of_mem_edges hp
    let q : T.graph.Walk c.vertex B.root := p.takeUntil B.root hrootSupp
    have hqChild : s(c.vertex, B.root) ∉ q.edges := by
      intro hq
      exact hchildEdge (p.edges_takeUntil_subset_edges hrootSupp hq)
    have hreachRoot :
        (T.graph.deleteEdges {s(c.vertex, B.root)}).Reachable c.vertex B.root :=
      SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr ⟨q, hqChild⟩
    have hbridge : T.graph.IsBridge s(c.vertex, B.root) :=
      (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp T.isTree.isAcyclic) c.adj.symm
    exact (SimpleGraph.isBridge_iff.mp hbridge) hreachRoot
  have hreachInParent :
      B.deletedGraph.Reachable c.vertex x := by
    simpa [deletedGraph] using
      (SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr ⟨p, hparentEdge⟩)
  have hrootChild :
      B.deletedGraph.Adj B.root c.vertex := by
    rw [deletedGraph, SimpleGraph.deleteEdges_adj]
    refine ⟨c.adj, ?_⟩
    simpa using B.childEdge_ne_boundary c
  have hrootReach : B.deletedGraph.Reachable B.root x :=
    hrootChild.reachable.trans hreachInParent
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff, component]
  exact (SimpleGraph.ConnectedComponent.sound hrootReach).symm
end TreeStack.OrientedBranch
