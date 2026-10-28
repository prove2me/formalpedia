-- Prove2me | solution 1 for WilliamsonShmoys.component_edge_count_aggregation_induced_edge_count_sum.edge_equiv_sigma
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:45:49.317198+00:00
-- url     : https://prove2.me/submissions/aa50f748-d751-4ead-88cb-a3cf6591fa11

import Mathlib

set_option autoImplicit false

open scoped Classical

theorem S181agg (V : Type) [Fintype V]
    (H : SimpleGraph V)
    (C : Finset (Finset V))
    (hPartition : (∀ S ∈ C, S.Nonempty) ∧
      ∀ v : V, ∃! S : Finset V, S ∈ C ∧ v ∈ S)
    (hNoCross : ∀ ⦃u v : V⦄, H.Adj u v →
      ∃ S ∈ C, u ∈ S ∧ v ∈ S) :
    H.edgeSet.ncard =
      C.sum (fun S => (H.induce (↑S : Set V)).edgeSet.ncard) := by
  classical
  let A : Finset V → Finset (Sym2 V) := fun S =>
    (H.induce (↑S : Set V)).edgeFinset.image (Sym2.map Subtype.val)
  have hA : ∀ S, (A S).card = (H.induce (↑S : Set V)).edgeSet.ncard := by
    intro S
    rw [Finset.card_image_of_injective _ (Sym2.map.injective Subtype.val_injective),
      ← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
  have hmem : ∀ S (e : Sym2 V), e ∈ A S →
      e ∈ H.edgeSet ∧ ∀ x ∈ e, x ∈ S := by
    intro S e he
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 he
    rw [SimpleGraph.mem_edgeFinset] at he'
    induction e' using Sym2.ind with
    | h x y =>
      refine ⟨by simpa using he', fun z hz => ?_⟩
      rw [Sym2.map_mk, Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · exact x.2
      · exact y.2
  have hunion : H.edgeFinset = C.biUnion A := by
    ext e
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_biUnion]
      constructor
      · intro h
        obtain ⟨S, hS, ha, hb⟩ := hNoCross h
        refine ⟨S, hS, Finset.mem_image.2 ⟨s(⟨a, ha⟩, ⟨b, hb⟩), ?_, by simp⟩⟩
        rw [SimpleGraph.mem_edgeFinset]
        simpa using h
      · rintro ⟨S, -, he⟩
        exact (hmem S _ he).1
  have hE : H.edgeSet = ((C.biUnion A : Finset (Sym2 V)) : Set (Sym2 V)) := by
    rw [← hunion, SimpleGraph.coe_edgeFinset]
  rw [hE, Set.ncard_coe_finset, Finset.card_biUnion]
  · exact Finset.sum_congr rfl (fun S _ => hA S)
  · intro S hS T hT hST
    rw [Function.onFun, Finset.disjoint_left]
    intro e heS heT
    obtain ⟨e', -, rfl⟩ := Finset.mem_image.1 heS
    induction e' using Sym2.ind with
    | h x y =>
      have h1 := (hmem S _ heS).2 x.1 (by simp)
      have h2 := (hmem T _ heT).2 x.1 (by simp)
      obtain ⟨R, -, hR⟩ := hPartition.2 x.1
      exact hST ((hR S ⟨hS, h1⟩).trans (hR T ⟨hT, h2⟩).symm)

theorem solution
    {V : Type} [Fintype V] (H : SimpleGraph V) (C : Finset (Finset V))
    (hPartition : (∀ S ∈ C, S.Nonempty) ∧
      ∀ v : V, ∃! S : Finset V, S ∈ C ∧ v ∈ S)
    (hNoCross : ∀ ⦃u v : V⦄, H.Adj u v →
      ∃ S ∈ C, u ∈ S ∧ v ∈ S) :
    Nonempty (H.edgeSet ≃
      Σ S : C, {e : Sym2 (↑(S : Finset V)) //
        e ∈ (H.induce (↑(S : Finset V) : Set V)).edgeSet}) := by
  classical
  rw [← Finite.card_eq, Nat.card_sigma, Nat.card_coe_set_eq,
    S181agg V H C hPartition hNoCross, ← Finset.sum_coe_sort C]
  rfl
