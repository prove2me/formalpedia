-- Prove2me | solution 1 for WilliamsonShmoys.connectedComponent_edge_conservation_disjoint__p2m_1c5fc6d8_f74d_4a49_af67_c6124a04288f_a2
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-10T17:49:47.36673+00:00
-- url     : https://prove2.me/submissions/481eacee-08df-418e-83cc-d6e976040848

import Mathlib

open scoped BigOperators

set_option autoImplicit false

/-- If a family of pairwise disjoint vertex blocks covers every edge of `L`, then the edge counts of
the induced subgraphs on the blocks sum to the edge count of `L`. -/
theorem solution {V : Type*} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    (dL : DecidableRel L.Adj) (C : Finset (Finset V))
    (hdisj : ∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t)
    (hpair : ∀ u v : V, L.Adj u v → ∃ s ∈ C, u ∈ s ∧ v ∈ s) :
    (letI : DecidableRel L.Adj := dL;
      (∑ s ∈ C, (L.induce (↑s : Set V)).edgeFinset.card) = L.edgeFinset.card) := by
  classical
  set B : Finset V → Finset (Sym2 V) := fun s => L.edgeFinset ∩ s.sym2 with hB
  have hterm : ∀ s ∈ C, (L.induce (↑s : Set V)).edgeFinset.card = (B s).card := by
    intro s hs
    rw [← SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := L) (s := s)]
    rw [SimpleGraph.filter_edgeFinset_toFinset_subset]
  have hnonempty : ∀ e : Sym2 V, e.toFinset.Nonempty := by
    intro e
    induction e using Sym2.ind with
    | _ u v => exact ⟨u, by simp⟩
  have hcover : C.biUnion B = L.edgeFinset := by
    ext e
    constructor
    · intro he
      rw [Finset.mem_biUnion] at he
      obtain ⟨s, -, hs⟩ := he
      exact (Finset.mem_inter.mp hs).1
    · intro he
      revert he
      induction e using Sym2.ind with
      | _ u v =>
        intro he
        have h1 : s(u, v) ∈ L.edgeSet := by simpa [SimpleGraph.edgeFinset] using he
        have hadj : L.Adj u v := (SimpleGraph.mem_edgeSet L).mp h1
        obtain ⟨s, hsC, hu, hv⟩ := hpair u v hadj
        refine Finset.mem_biUnion.mpr ⟨s, hsC, ?_⟩
        simp only [hB, Finset.mem_inter]
        refine ⟨he, ?_⟩
        rw [Finset.mem_sym2_iff]
        intro a ha
        rcases Sym2.mem_iff.mp ha with h | h
        · rw [h]; exact hu
        · rw [h]; exact hv
  have hdisjB : ((C : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint B := by
    intro s hs t ht hst
    change Disjoint (B s) (B t)
    rw [Finset.disjoint_left]
    intro e he he'
    simp only [hB, Finset.mem_inter] at he he'
    rw [Finset.mem_sym2_iff] at he he'
    obtain ⟨a, ha⟩ := hnonempty e
    have ha' : a ∈ e := by rwa [Sym2.mem_toFinset] at ha
    exact (Finset.disjoint_left.mp (hdisj s hs t ht hst) (he.2 a ha') (he'.2 a ha'))
  have hcard : L.edgeFinset.card = ∑ s ∈ C, (B s).card := by
    rw [← hcover, Finset.card_biUnion hdisjB]
  calc (∑ s ∈ C, (L.induce (↑s : Set V)).edgeFinset.card) = ∑ s ∈ C, (B s).card :=
        Finset.sum_congr rfl hterm
    _ = L.edgeFinset.card := hcard.symm
