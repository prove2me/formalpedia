-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_from_component_estimates_937ee64a84854eee
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:44:49.852564+00:00
-- url     : https://prove2.me/submissions/de1862f6-598d-4d98-8da0-58567c4f1948

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
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hm : 2 ≤ L.edgeSet.ncard)
    (hlocal : ∀ (C : L.ConnectedComponent), ∀ [Fintype (↑C.supp)],
      3 ≤ Fintype.card (↑C.supp) →
        (L.induce C.supp).edgeSet.ncard + 6 ≤ 3 * Fintype.card (↑C.supp)) :
    L.edgeSet.ncard + 3 * Nat.card L.ConnectedComponent + 3 ≤
      3 * Fintype.card V := by
  have hE := edgeSum L
  have hS := suppSum L
  have hC : ∀ C : L.ConnectedComponent, 3 ≤ C.supp.ncard →
      (L.induce C.supp).edgeSet.ncard + 6 ≤ 3 * C.supp.ncard := by
    intro C h3
    classical
    have := hlocal C
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at this
    exact this h3
  let g : L.ConnectedComponent → ℕ := fun C =>
    if 3 ≤ C.supp.ncard then 3 else 2 * (L.induce C.supp).edgeSet.ncard
  have hloc : ∀ C : L.ConnectedComponent,
      (L.induce C.supp).edgeSet.ncard + 3 + g C ≤ 3 * C.supp.ncard := by
    intro C
    have hpos : 1 ≤ C.supp.ncard := by
      obtain ⟨v, hv⟩ := C.nonempty_supp
      exact Nat.one_le_iff_ne_zero.mpr (Set.ncard_ne_zero_of_mem hv)
    have hch : (L.induce C.supp).edgeSet.ncard ≤ (C.supp.ncard).choose 2 := by
      classical
      have h1 := (L.induce C.supp).card_edgeFinset_le_card_choose_two
      rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset] at h1
      rwa [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at h1
    by_cases h3 : 3 ≤ C.supp.ncard
    · simp only [g, if_pos h3]; have := hC C h3; omega
    · simp only [g, if_neg h3]
      interval_cases hn : C.supp.ncard
      · simp at hch; omega
      · have : (2:ℕ).choose 2 = 1 := by decide
        omega
  have hsum : ∑ C : L.ConnectedComponent, ((L.induce C.supp).edgeSet.ncard + 3 + g C) ≤
      ∑ C : L.ConnectedComponent, 3 * C.supp.ncard := Finset.sum_le_sum fun C _ => hloc C
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hE, hS] at hsum
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card] at hsum
  have hg : 3 ≤ ∑ C : L.ConnectedComponent, g C := by
    by_cases hbig : ∃ C : L.ConnectedComponent, 3 ≤ C.supp.ncard
    · obtain ⟨C, hC3⟩ := hbig
      have : g C = 3 := by simp [g, hC3]
      rw [← this]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ C)
    · push_neg at hbig
      have : ∑ C : L.ConnectedComponent, g C =
          2 * ∑ C : L.ConnectedComponent, (L.induce C.supp).edgeSet.ncard := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun C _ => by simp [g, Nat.not_le.mpr (hbig C)]
      rw [this, hE]; omega
  have := Nat.card_eq_fintype_card (α := V)
  omega
