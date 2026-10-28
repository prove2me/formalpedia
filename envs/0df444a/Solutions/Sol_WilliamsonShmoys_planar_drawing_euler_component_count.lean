-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_component_count
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:00:18.514722+00:00
-- url     : https://prove2.me/submissions/9102310f-1b0b-4521-9a1e-9d32c442d3a2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
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

open SimpleGraph WilliamsonShmoys in
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + Nat.card L.ConnectedComponent + 1 ∧
      1 ≤ Nat.card L.ConnectedComponent := by
  have hE := edgeSum L
  have hS := suppSum L
  have hC : ∀ C : L.ConnectedComponent, C.supp.ncard ≤ (L.induce C.supp).edgeSet.ncard + 1 := by
    intro C
    have h := (ConnectedComponent.connected_toSimpleGraph C).card_vert_le_card_edgeSet_add_one
    rw [Nat.card_coe_set_eq] at h
    exact h
  have hsum : ∑ C : L.ConnectedComponent, C.supp.ncard ≤
      ∑ C : L.ConnectedComponent, ((L.induce C.supp).edgeSet.ncard + 1) :=
    Finset.sum_le_sum fun C _ => hC C
  rw [Finset.sum_add_distrib, hE, hS] at hsum
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    ← Nat.card_eq_fintype_card] at hsum
  have hn := Nat.card_eq_fintype_card (α := V)
  obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hk : 1 ≤ Nat.card L.ConnectedComponent :=
    Nat.one_le_iff_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨⟨L.connectedComponentMk v⟩, inferInstance⟩)
  exact ⟨L.edgeSet.ncard + Nat.card L.ConnectedComponent + 1 - Fintype.card V, by omega, hk⟩
