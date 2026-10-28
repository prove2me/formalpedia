-- Prove2me | solution 1 for WilliamsonShmoys.aggregate_connected_component_edge_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T22:46:37.524521+00:00
-- url     : https://prove2.me/submissions/5974dcbb-9d2e-41a7-8c5d-ee1ec472f1bc

import Mathlib
open SimpleGraph in
theorem edgeSum
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) :
    (∑ C : K.ConnectedComponent, (K.induce C.supp).edgeSet.ncard) =
      K.edgeSet.ncard := by
  classical
  let f : Sym2 V → K.ConnectedComponent := fun e => K.connectedComponentMk e.out.1
  have hmem : ∀ e ∈ K.edgeSet, ∀ v ∈ e, K.connectedComponentMk v = f e := by
    intro e he v hv
    have h1 : e.out.1 ∈ e := Sym2.out_fst_mem e
    induction e using Sym2.ind with
    | h a b =>
      have hab : K.connectedComponentMk a = K.connectedComponentMk b :=
        ConnectedComponent.eq.mpr (SimpleGraph.Adj.reachable he)
      rcases Sym2.mem_iff.mp hv with rfl | rfl <;>
        rcases Sym2.mem_iff.mp h1 with h | h <;> simp only [f, h, hab]
  have himg : ∀ C : K.ConnectedComponent,
      Sym2.map Subtype.val '' (K.induce C.supp).edgeSet = {e ∈ K.edgeSet | f e = C} := by
    intro C
    ext e
    constructor
    · rintro ⟨e', he', rfl⟩
      induction e' using Sym2.ind with
      | h a b =>
        have hab : K.Adj a.1 b.1 := he'
        refine ⟨hab, ?_⟩
        rw [← hmem _ hab a.1 (by simp)]
        exact a.2
    · intro ⟨he, hfe⟩
      induction e using Sym2.ind with
      | h a b =>
        have ha : a ∈ C.supp := by
          rw [ConnectedComponent.mem_supp_iff, hmem _ he a (by simp), hfe]
        have hb : b ∈ C.supp := by
          rw [ConnectedComponent.mem_supp_iff, hmem _ he b (by simp), hfe]
        exact ⟨s(⟨a, ha⟩, ⟨b, hb⟩), he, rfl⟩
  have hcard : ∀ C : K.ConnectedComponent,
      (K.induce C.supp).edgeSet.ncard = {e ∈ K.edgeSet | f e = C}.ncard := by
    intro C
    rw [← himg C, Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]
  simp_rw [hcard]
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset,
    Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr (by ext; simp) fun C _ => ?_
  rw [← Set.ncard_coe_finset]
  congr 1
  ext e
  simp

theorem suppSum
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) :
    (∑ C : K.ConnectedComponent, C.supp.ncard) = Fintype.card V := by
  classical
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise
    (f := K.connectedComponentMk) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr (by ext; simp) fun C _ => ?_
  rw [← Set.ncard_coe_finset]
  congr 1
  ext v
  simp [SimpleGraph.ConnectedComponent.mem_supp_iff]

open SimpleGraph in
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hC : ∀ C : K.ConnectedComponent,
      3 ≤ C.supp.ncard →
      (K.induce C.supp).edgeSet.ncard + 6 ≤ 3 * C.supp.ncard) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  have hE := edgeSum K
  have hS := suppSum K
  have hsmall : ∀ C : K.ConnectedComponent,
      (K.induce C.supp).edgeSet.ncard + 3 ≤ 3 * C.supp.ncard := by
    intro C
    classical
    have hpos : 1 ≤ C.supp.ncard := by
      obtain ⟨v, hv⟩ := C.nonempty_supp
      exact Nat.one_le_iff_ne_zero.mpr (Set.ncard_ne_zero_of_mem hv)
    have hch : (K.induce C.supp).edgeSet.ncard ≤ (C.supp.ncard).choose 2 := by
      have h1 := (K.induce C.supp).card_edgeFinset_le_card_choose_two
      rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset] at h1
      rwa [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at h1
    by_cases h3 : 3 ≤ C.supp.ncard
    · have := hC C h3; omega
    · have hc2 : (C.supp.ncard).choose 2 + 3 ≤ 3 * C.supp.ncard := by
        interval_cases C.supp.ncard <;> decide
      omega
  by_cases hk : 2 ≤ Nat.card K.ConnectedComponent
  · have hsum : ∑ C : K.ConnectedComponent, ((K.induce C.supp).edgeSet.ncard + 3) ≤
        ∑ C : K.ConnectedComponent, 3 * C.supp.ncard := Finset.sum_le_sum fun C _ => hsmall C
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hE, hS] at hsum
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card] at hsum
    have := Nat.card_eq_fintype_card (α := V)
    omega
  · obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    set C := K.connectedComponentMk v
    have hsub : ∀ D : K.ConnectedComponent, D = C := by
      intro D
      have : Nat.card K.ConnectedComponent ≤ 1 := by omega
      have : Subsingleton K.ConnectedComponent := (Finite.card_le_one_iff_subsingleton).mp this
      exact Subsingleton.elim D C
    rw [Finset.sum_eq_single C (fun D _ h => absurd (hsub D) h) (by simp)] at hE hS
    have := hC C (by omega)
    omega
