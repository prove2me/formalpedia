-- Prove2me | solution 1 for WilliamsonShmoys.partition_edge_count_additive__p2m_637ed7a6_3035_49c1_aba6_5023ef3aefa9_a1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T23:32:02.718407+00:00
-- url     : https://prove2.me/submissions/4ac642e5-aba0-405c-bc0f-bbdcea924d97

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
open SimpleGraph

theorem part_eq_of_shared_vertex {V : Type} [DecidableEq V]
    (parts : Finset (Finset V))
    (huniq : ∀ v : V, ∃! W : Finset V, W ∈ parts ∧ v ∈ W)
    (A B : Finset V) (hA : A ∈ parts) (hB : B ∈ parts)
    (v : V) (ha : v ∈ A) (hb : v ∈ B) : A = B := by
  have hA_v : A ∈ parts ∧ v ∈ A := ⟨hA, ha⟩
  have hB_v : B ∈ parts ∧ v ∈ B := ⟨hB, hb⟩
  exact ExistsUnique.unique (huniq v) hA_v hB_v

def partHom {V : Type} (M : SimpleGraph V) (W : Finset V) :
    (M.induce (W : Set V)) →g M where
  toFun x := x.val
  map_rel' := id

noncomputable def flattenPartitionEdges {V : Type} (M : SimpleGraph V)
    (parts : Finset (Finset V))
    (x : Σ W : ↑parts, (M.induce (W.val : Set V)).edgeSet) : M.edgeSet :=
  (partHom M x.1.val).mapEdgeSet x.2

noncomputable def partitionOwner {V : Type} [DecidableEq V] (M : SimpleGraph V)
    (parts : Finset (Finset V))
    (huniq : ∀ v : V, ∃! W : Finset V, W ∈ parts ∧ v ∈ W)
    (e : M.edgeSet) : ↑parts :=
  ⟨Classical.choose (huniq e.val.out.1).exists,
    (Classical.choose_spec (huniq e.val.out.1).exists).1⟩

theorem owner_flatten {V : Type} [DecidableEq V] (M : SimpleGraph V)
    (parts : Finset (Finset V))
    (huniq : ∀ v : V, ∃! W : Finset V, W ∈ parts ∧ v ∈ W)
    (W : ↑parts) (e : (M.induce (W.val : Set V)).edgeSet) :
    partitionOwner M parts huniq (flattenPartitionEdges M parts ⟨W, e⟩) = W := by
  let z := (flattenPartitionEdges M parts ⟨W, e⟩).val
  have hz : z.out.1 ∈ z := Sym2.out_fst_mem z
  change z.out.1 ∈ Sym2.map Subtype.val e.val at hz
  obtain ⟨u, _, hu⟩ := Sym2.mem_map.mp hz
  have ho : z.out.1 ∈ (partitionOwner M parts huniq (flattenPartitionEdges M parts ⟨W,e⟩)).val :=
    (Classical.choose_spec (huniq z.out.1).exists).2
  have hw : z.out.1 ∈ W.val := by
    rw [← hu]
    exact u.property
  apply Subtype.ext
  exact part_eq_of_shared_vertex parts huniq _ _
    (partitionOwner M parts huniq (flattenPartitionEdges M parts ⟨W,e⟩)).property W.property z.out.1 ho hw

theorem flattenPartitionEdges_injective {V : Type} [DecidableEq V] (M : SimpleGraph V)
    (parts : Finset (Finset V))
    (huniq : ∀ v : V, ∃! W : Finset V, W ∈ parts ∧ v ∈ W) :
    Function.Injective (flattenPartitionEdges M parts) := by
  intro ⟨C, e⟩ ⟨D, f⟩ h
  have hc : C = D := by
    rw [← owner_flatten M parts huniq C e, ← owner_flatten M parts huniq D f, h]
  cases hc
  have he : e = f := by
    apply Hom.mapEdgeSet.injective (partHom M C.val) Subtype.val_injective
    exact h
  cases he
  rfl

theorem flattenPartitionEdges_surjective {V : Type} (M : SimpleGraph V)
    (parts : Finset (Finset V))
    (hclosed : ∀ u v : V, M.Adj u v → ∃ W ∈ parts, u ∈ W ∧ v ∈ W) :
    Function.Surjective (flattenPartitionEdges M parts) := by
  intro e
  let u := e.val.out.1
  let v := e.val.out.2
  have hadj : M.Adj u v := by
    change s(u, v) ∈ M.edgeSet
    have heq : s(u, v) = e.val := e.val.out_eq
    rw [heq]
    exact e.property
  obtain ⟨W, hW, hu, hv⟩ := hclosed u v hadj
  let localEdge : (M.induce (W : Set V)).edgeSet :=
    ⟨s(⟨u, hu⟩, ⟨v, hv⟩), by exact hadj⟩
  refine ⟨⟨⟨W, hW⟩, localEdge⟩, ?_⟩
  apply Subtype.ext
  change Sym2.map Subtype.val localEdge.val = e.val
  change s(u, v) = e.val
  exact e.val.out_eq

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V)
    (parts : Finset (Finset V))
    (huniq : ∀ v : V, ∃! W : Finset V, W ∈ parts ∧ v ∈ W)
    (hclosed : ∀ u v : V, M.Adj u v → ∃ W ∈ parts, u ∈ W ∧ v ∈ W) :
    M.edgeSet.ncard = ∑ W ∈ parts, (M.induce (W : Set V)).edgeSet.ncard := by
  classical
  let eqv := Equiv.ofBijective (flattenPartitionEdges M parts)
    ⟨flattenPartitionEdges_injective M parts huniq, flattenPartitionEdges_surjective M parts hclosed⟩
  have hh := Nat.card_congr eqv
  have hcard : M.edgeSet.ncard = ∑ i : ↑parts, (M.induce (i.val : Set V)).edgeSet.ncard := by
    simpa only [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_sigma] using hh.symm
  rw [hcard]
  exact Finset.sum_coe_sort parts (fun W => (M.induce (W : Set V)).edgeSet.ncard)

