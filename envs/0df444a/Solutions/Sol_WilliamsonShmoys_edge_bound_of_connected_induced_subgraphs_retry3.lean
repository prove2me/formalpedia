-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_of_connected_induced_subgraphs_retry3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T19:18:17.316288+00:00
-- url     : https://prove2.me/submissions/672c9ae4-9e03-4401-b0fe-b633ecc35b31

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem S191EY_cvp
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) :
    ∃ parts : Finset (Finset V),
      (∀ C ∈ parts, C.Nonempty) ∧
      (∀ C ∈ parts, ∀ D ∈ parts, C ≠ D → Disjoint C D) ∧
      parts.biUnion id = Finset.univ ∧
      (∀ u v, G.Adj u v → ∃ C ∈ parts, u ∈ C ∧ v ∈ C) ∧
      (∀ C ∈ parts, (G.induce (fun v => v ∈ C)).Connected) := by
  classical
  have : Fintype G.ConnectedComponent := Fintype.ofFinite _
  let f : G.ConnectedComponent → Finset V := fun c => c.supp.toFinset
  have hf : ∀ c : G.ConnectedComponent, ∀ v, v ∈ f c ↔ G.connectedComponentMk v = c := by
    intro c v
    simp only [f, Set.mem_toFinset, SimpleGraph.ConnectedComponent.mem_supp_iff]
  refine ⟨Finset.univ.image f, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro C ⟨c, rfl⟩
    exact ⟨c.out, (hf c _).2 c.out_eq⟩
  · simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro C ⟨c, rfl⟩ D ⟨d, rfl⟩ hne
    rw [Finset.disjoint_left]
    intro v hc hd
    rw [hf] at hc hd
    exact hne (by rw [← hc, ← hd])
  · ext v
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and, id, iff_true]
    exact ⟨f (G.connectedComponentMk v), ⟨_, rfl⟩, (hf _ _).2 rfl⟩
  · intro u v huv
    refine ⟨f (G.connectedComponentMk u), Finset.mem_image_of_mem _ (Finset.mem_univ _),
      (hf _ _).2 rfl, (hf _ _).2 ?_⟩
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj huv).symm
  · simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro C ⟨c, rfl⟩
    have h := (SimpleGraph.ConnectedComponent.maximal_connected_induce_supp c).1
    have hs : (fun v => v ∈ f c : Set V) = c.supp := by
      ext v
      change v ∈ f c ↔ v ∈ c.supp
      rw [hf, SimpleGraph.ConnectedComponent.mem_supp_iff]
    simp only at h
    rw [hs]
    exact h
open Classical Finset in
theorem S191EY_induce_card {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (C : Finset V) :
    (G.induce (fun v => v ∈ C)).edgeSet.ncard = #(G.edgeFinset ∩ C.sym2) := by
  classical
  have h := G.map_edgeFinset_induce (s := (C : Set V))
  have hc := congrArg Finset.card h
  rw [Finset.card_map] at hc
  simp only [Finset.toFinset_coe] at hc
  rw [← hc, ← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
  rfl

open Finset in
theorem S191EY_pec
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (parts : Finset (Finset V))
    (hdisjoint : ∀ C ∈ parts, ∀ D ∈ parts, C ≠ D → Disjoint C D)
    (hcover : parts.biUnion id = Finset.univ)
    (hadj : ∀ u v, G.Adj u v → ∃ C ∈ parts, u ∈ C ∧ v ∈ C) :
    G.edgeSet.ncard = ∑ C ∈ parts, (G.induce (fun v => v ∈ C)).edgeSet.ncard := by
  classical
  simp_rw [S191EY_induce_card]
  rw [← Finset.card_biUnion]
  · rw [Set.ncard_eq_toFinset_card' G.edgeSet]
    congr 1
    ext e
    induction e using Sym2.ind with
    | h u v =>
      simp only [Set.mem_toFinset, SimpleGraph.mem_edgeSet, Finset.mem_biUnion, Finset.mem_inter,
        SimpleGraph.mem_edgeFinset, Finset.mk_mem_sym2_iff]
      constructor
      · intro huv
        obtain ⟨C, hC, hu, hv⟩ := hadj u v huv
        exact ⟨C, hC, huv, hu, hv⟩
      · rintro ⟨C, -, huv, -⟩
        exact huv
  · intro C hC D hD hCD
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    rw [Finset.mem_inter] at he he'
    induction e using Sym2.ind with
    | h u v =>
      rw [Finset.mk_mem_sym2_iff] at he he'
      exact Finset.disjoint_left.1 (hdisjoint C hC D hD hCD) he.2.1 he'.2.1
theorem S191EY_small
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (C : Finset V)
    (hC : C.Nonempty)
    (hconn : (G.induce (fun v => v ∈ C)).Connected)
    (hsmall : C.card < 3) :
    (G.induce (fun v => v ∈ C)).edgeSet.ncard ≤ 3 * C.card - 3 := by
  classical
  have h1 := (G.induce (fun v => v ∈ C)).card_edgeFinset_le_card_choose_two
  rw [Set.ncard_eq_toFinset_card' (G.induce (fun v => v ∈ C)).edgeSet]
  rw [← SimpleGraph.edgeFinset] at *
  have hc : Fintype.card {v // v ∈ C} = C.card := Fintype.card_coe C
  have hpos := hC.card_pos
  have h2 : (G.induce (fun v => v ∈ C)).edgeFinset.card ≤ C.card.choose 2 := by
    rw [Fintype.card_subtype] at h1
    refine h1.trans (le_of_eq ?_)
    congr 2
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.rfl
  interval_cases h : C.card <;> simp_all <;> omega

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 <= Fintype.card V) (hbound : ∀ (S : Finset V), 3 <= S.card → (H.induce (↑S : Set V)).Connected → (H.induce (↑S : Set V)).edgeSet.ncard + 6 <= 3 * Fintype.card {v // v ∈ S}) : H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  classical
  obtain ⟨parts, hne, hdis, hcov, hadj, hconn⟩ := S191EY_cvp H
  have hE := S191EY_pec H parts hdis hcov hadj
  have hcard : ∑ C ∈ parts, C.card = Fintype.card V := by
    rw [← Finset.card_univ, ← hcov, Finset.card_biUnion]
    · rfl
    · intro C hC D hD hCD
      exact hdis C hC D hD hCD
  set E : Finset V → ℕ := fun C => (H.induce (fun v => v ∈ C)).edgeSet.ncard with hEdef
  have hsmall : ∀ C ∈ parts, C.card < 3 → 2 * E C ≤ C.card := by
    intro C hC h3
    have h := S191EY_small H C (hne C hC) (hconn C hC) h3
    have h2 : E C ≤ (C.card).choose 2 := by
      have h1 := (H.induce (fun v => v ∈ C)).card_edgeFinset_le_card_choose_two
      show (H.induce (fun v => v ∈ C)).edgeSet.ncard ≤ _
      rw [Set.ncard_eq_toFinset_card' (H.induce (fun v => v ∈ C)).edgeSet]
      rw [← SimpleGraph.edgeFinset]
      rw [Fintype.card_subtype] at h1
      refine h1.trans (le_of_eq ?_)
      congr 2
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Iff.rfl
    have hpos := (hne C hC).card_pos
    interval_cases hc : C.card <;> simp_all <;> omega
  have hbig : ∀ C ∈ parts, 3 ≤ C.card → E C + 6 ≤ 3 * C.card := by
    intro C hC h3
    have := hbound C h3 (hconn C hC)
    rw [Fintype.card_coe] at this
    exact this
  have hle : ∀ C ∈ parts, E C ≤ 3 * C.card := by
    intro C hC
    by_cases h3 : 3 ≤ C.card
    · have := hbig C hC h3; omega
    · have := hsmall C hC (by omega); omega
  rw [hE]
  change ∑ C ∈ parts, E C + 6 ≤ 3 * Fintype.card V
  rw [← hcard] at hV ⊢
  by_cases hex : ∃ C0 ∈ parts, 3 ≤ C0.card
  · obtain ⟨C0, hC0, h3⟩ := hex
    have a := Finset.add_sum_erase parts E hC0
    have b := Finset.add_sum_erase parts Finset.card hC0
    have h1 := hbig C0 hC0 h3
    have h2 : ∑ x ∈ parts.erase C0, E x ≤ ∑ x ∈ parts.erase C0, 3 * x.card :=
      Finset.sum_le_sum fun C hC => hle C (Finset.mem_of_mem_erase hC)
    rw [← Finset.mul_sum] at h2
    omega
  · push_neg at hex
    have h2 : 2 * ∑ C ∈ parts, E C ≤ ∑ C ∈ parts, C.card := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun C hC => hsmall C hC (hex C hC)
    omega
