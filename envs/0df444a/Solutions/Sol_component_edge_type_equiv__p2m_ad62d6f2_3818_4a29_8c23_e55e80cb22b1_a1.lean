-- Prove2me | solution 1 for component_edge_type_equiv__p2m_ad62d6f2_3818_4a29_8c23_e55e80cb22b1_a1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T23:26:12.857356+00:00
-- url     : https://prove2.me/submissions/98ad96df-0bab-4995-8b57-adae5c38a46e

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Set.Card

set_option autoImplicit false
open SimpleGraph

noncomputable def flattenEdges {V : Type} (G : SimpleGraph V)
    (x : Σ C : G.ConnectedComponent, C.toSimpleGraph.edgeSet) : G.edgeSet :=
  x.1.toSimpleGraph_hom.mapEdgeSet x.2

noncomputable def edgeComponent {V : Type} (G : SimpleGraph V)
    (e : G.edgeSet) : G.ConnectedComponent :=
  G.connectedComponentMk e.val.out.1

theorem edgeComponent_flatten {V : Type} (G : SimpleGraph V)
    (C : G.ConnectedComponent) (e : C.toSimpleGraph.edgeSet) :
    edgeComponent G (flattenEdges G ⟨C, e⟩) = C := by
  let z := (flattenEdges G ⟨C, e⟩).val
  have hz : z.out.1 ∈ z := Sym2.out_fst_mem z
  change z.out.1 ∈ Sym2.map Subtype.val e.val at hz
  obtain ⟨u, _, hu⟩ := Sym2.mem_map.mp hz
  change G.connectedComponentMk z.out.1 = C
  rw [← hu]
  exact u.property

theorem flattenEdges_injective {V : Type} (G : SimpleGraph V) :
    Function.Injective (flattenEdges G) := by
  intro ⟨C, e⟩ ⟨D, f⟩ h
  have hc : C = D := by
    rw [← edgeComponent_flatten G C e, ← edgeComponent_flatten G D f, h]
  cases hc
  have he : e = f := by
    apply Hom.mapEdgeSet.injective C.toSimpleGraph_hom Subtype.val_injective
    exact h
  cases he
  rfl

theorem flattenEdges_surjective {V : Type} (G : SimpleGraph V) :
    Function.Surjective (flattenEdges G) := by
  intro e
  let u := e.val.out.1
  let v := e.val.out.2
  let C := G.connectedComponentMk u
  have hadj : G.Adj u v := by
    change s(u, v) ∈ G.edgeSet
    have heq : s(u, v) = e.val := e.val.out_eq
    rw [heq]
    exact e.property
  have hu : u ∈ C.supp := by rfl
  have hv : v ∈ C.supp := by
    change G.connectedComponentMk v = G.connectedComponentMk u
    exact (ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm
  let localEdge : C.toSimpleGraph.edgeSet :=
    ⟨s(⟨u, hu⟩, ⟨v, hv⟩), by exact hadj⟩
  refine ⟨⟨C, localEdge⟩, ?_⟩
  apply Subtype.ext
  change Sym2.map Subtype.val localEdge.val = e.val
  change s(u, v) = e.val
  exact e.val.out_eq

theorem solution {V : Type} (G : SimpleGraph V) :
    Nonempty (G.edgeSet ≃ Σ C : G.ConnectedComponent, C.toSimpleGraph.edgeSet) := by
  exact ⟨(Equiv.ofBijective (flattenEdges G) ⟨flattenEdges_injective G, flattenEdges_surjective G⟩).symm⟩

