-- Prove2me | solution 2 for WilliamsonShmoys.connected_component_partition_edge_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T19:10:37.565887+00:00
-- url     : https://prove2.me/submissions/51b57eca-d2fe-4412-940a-d2cd96912e17

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

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) :
    ∃ parts : Finset (Finset V),
      (∀ C ∈ parts, C.Nonempty) ∧
      (∀ C ∈ parts, ∀ D ∈ parts, C ≠ D → Disjoint C D) ∧
      parts.biUnion id = Finset.univ ∧
      G.edgeSet.ncard = ∑ C ∈ parts, (G.induce (fun v => v ∈ C)).edgeSet.ncard ∧
      (∀ C ∈ parts, (G.induce (fun v => v ∈ C)).Connected) := by
  obtain ⟨parts, h1, h2, h3, h4, h5⟩ := S191EY_cvp G
  exact ⟨parts, h1, h2, h3, S191EY_pec G parts h2 h3 h4, h5⟩
