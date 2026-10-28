-- Prove2me | solution 1 for WilliamsonShmoys.partition_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T18:58:46.388243+00:00
-- url     : https://prove2.me/submissions/fdbb2517-617b-4350-b690-5b9683c05996

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
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
theorem solution
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
