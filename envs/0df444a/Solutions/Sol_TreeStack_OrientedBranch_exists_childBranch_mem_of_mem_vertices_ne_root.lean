-- Prove2me | solution 1 for TreeStack.OrientedBranch.exists_childBranch_mem_of_mem_vertices_ne_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:15:10.321106+00:00
-- url     : https://prove2.me/submissions/c7f6d2d6-f659-48d4-a848-e5b5c1a8b9c9

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch
import Theorems.Thm_TreeStack_OrientedBranch_root_ne_parent
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_root
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_parent
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
theorem _root_.solution
    (B : OrientedBranch T) {x : V}
    (hx : x ∈ B.vertices) (hxr : x ≠ B.root) :
    ∃ c : B.Child, x ∈ (B.childBranch c).vertices := by
  classical
  have hxComp : x ∈ B.component.supp := by
    simpa [vertices] using hx
  have hrComp : B.root ∈ B.component.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hreach : B.deletedGraph.Reachable B.root x :=
    B.component.reachable_of_mem_supp hrComp hxComp
  rcases hreach.exists_isPath with ⟨p, hp⟩
  rcases SimpleGraph.Walk.exists_eq_cons_of_ne hxr.symm p with
    ⟨v, hrv, p', hpEq⟩
  rw [hpEq] at hp
  have hpData :=
    (SimpleGraph.Walk.cons_isPath_iff hrv p').mp hp
  have hrootNot : B.root ∉ p'.support := hpData.2
  have hrvData := hrv
  rw [deletedGraph, SimpleGraph.deleteEdges_adj] at hrvData
  rcases hrvData with ⟨hrvT, hedge⟩
  have hvne : v ≠ B.parent := by
    intro hvp
    subst v
    simp at hedge
  let c : B.Child :=
    { vertex := v
      adj := hrvT
      ne_parent := hvne }
  have hle : B.deletedGraph ≤ T.graph := by
    intro a b hab
    rw [deletedGraph, SimpleGraph.deleteEdges_adj] at hab
    exact hab.1
  let q : T.graph.Walk v x := p'.mapLe hle
  have havoid : s(v, B.root) ∉ q.edges := by
    intro he
    have he' : s(v, B.root) ∈ p'.edges := by
      simpa [q, SimpleGraph.Walk.edges_mapLe_eq_edges] using he
    exact hrootNot (p'.snd_mem_support_of_mem_edges he')
  let q' : (T.graph.deleteEdges {s(v, B.root)}).Walk v x :=
    q.toDeleteEdges {s(v, B.root)} (by
      intro e he
      simp only [Set.mem_singleton_iff]
      intro heq
      subst e
      exact havoid he)
  have hreachChild :
      (B.childBranch c).deletedGraph.Reachable c.vertex x := by
    change (T.graph.deleteEdges {s(v, B.root)}).Reachable v x
    exact ⟨q'⟩
  refine ⟨c, ?_⟩
  rw [vertices, Set.mem_toFinset,
    SimpleGraph.ConnectedComponent.mem_supp_iff, component]
  exact (SimpleGraph.ConnectedComponent.sound hreachChild).symm
end TreeStack.OrientedBranch
