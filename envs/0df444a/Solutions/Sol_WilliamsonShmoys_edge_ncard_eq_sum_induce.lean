-- Prove2me | solution 1 for WilliamsonShmoys.edge_ncard_eq_sum_induce
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T19:26:00.317866+00:00
-- url     : https://prove2.me/submissions/0acea5f7-b974-4c20-858c-de92f8b9534e

import Mathlib
theorem solution
    {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) (C : Finset (Finset V))
    (hcover : ∀ v : V, ∃ S, S ∈ C ∧ v ∈ S)
    (hdisjoint : ∀ S, S ∈ C → ∀ T, T ∈ C → S ≠ T → Disjoint S T)
    (hadj : ∀ ⦃u v : V⦄, G.Adj u v → ∃ S, S ∈ C ∧ u ∈ S ∧ v ∈ S) :
    G.edgeSet.ncard = ∑ S ∈ C, (G.induce (↑S : Set V)).edgeSet.ncard := by
  classical
  let E : Finset V → Set (Sym2 V) := fun S => {e | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S}
  have himg : ∀ S : Finset V,
      Sym2.map Subtype.val '' (G.induce (↑S : Set V)).edgeSet = E S := by
    intro S
    ext e
    induction e using Sym2.ind with
    | _ a b =>
    constructor
    · rintro ⟨f, hf, hfe⟩
      induction f using Sym2.ind with
      | _ x y =>
      simp only [Sym2.map_pair_eq] at hfe
      rw [← hfe]
      refine ⟨by simpa using hf, ?_⟩
      intro v hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact x.2
      · exact y.2
    · rintro ⟨h1, h2⟩
      have ha : a ∈ (↑S : Set V) := h2 a (Sym2.mem_mk_left a b)
      have hb : b ∈ (↑S : Set V) := h2 b (Sym2.mem_mk_right a b)
      exact ⟨s(⟨a, ha⟩, ⟨b, hb⟩), by simpa using h1, rfl⟩
  have hcardS : ∀ S : Finset V, (G.induce (↑S : Set V)).edgeSet.ncard = (E S).ncard := by
    intro S
    rw [← himg S, Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]
  have hunion : G.edgeSet = ⋃ S ∈ C, E S := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
    simp only [Set.mem_iUnion]
    constructor
    · intro h
      obtain ⟨S, hS, ha, hb⟩ := hadj h
      refine ⟨S, hS, h, ?_⟩
      intro v hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact ha
      · exact hb
    · rintro ⟨S, -, h, -⟩; exact h
  rw [Finset.sum_congr rfl (fun S _ => hcardS S), hunion]
  rw [Set.ncard_eq_toFinset_card' (⋃ S ∈ C, E S)]
  have hfin : ∀ S, (E S).Finite := fun S => Set.toFinite _
  have : (⋃ S ∈ C, E S).toFinset = C.biUnion (fun S => (E S).toFinset) := by
    ext e; simp
  have hdis : (↑C : Set (Finset V)).PairwiseDisjoint (fun S => (E S).toFinset) := by
    intro S hS T hT hne
    rw [Function.onFun, Finset.disjoint_left]
    intro e he1 he2
    simp only [Set.mem_toFinset] at he1 he2
    obtain ⟨v, hv⟩ : ∃ v, v ∈ e := ⟨e.out.1, Sym2.out_fst_mem e⟩
    exact Finset.disjoint_left.mp (hdisjoint S hS T hT hne) (he1.2 v hv) (he2.2 v hv)
  rw [this, Finset.card_biUnion hdis]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  convert (Set.ncard_eq_toFinset_card' (E S)).symm
