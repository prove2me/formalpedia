-- Prove2me | solution 1 for WilliamsonShmoys.planar_component_edge_aggregation__p2m_98235c6f_660a_40d6_a6c4_218b22f2584f_a1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T13:28:09.29325+00:00
-- url     : https://prove2.me/submissions/d9a2e9a9-f9c8-4d69-9aeb-fefd1cdbae48

import Mathlib

open scoped BigOperators

set_option autoImplicit false

/-- If a family of vertex blocks covers every edge of `M`, then the edge counts of the induced
subgraphs on the blocks sum to at least the edge count of `M`. -/
theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V)
    (parts : Finset (Finset V))
    (hcover : ∀ v, ∃ C, C ∈ parts ∧ v ∈ C)
    (hdisjoint : ∀ C, C ∈ parts → ∀ D, D ∈ parts → C ≠ D → Disjoint C D)
    (hadj : ∀ u v, M.Adj u v → ∃ C, C ∈ parts ∧ u ∈ C ∧ v ∈ C) :
    M.edgeSet.ncard ≤ ∑ C ∈ parts, (M.induce (C : Set V)).edgeSet.ncard := by
  classical
  set B : Finset V → Finset (Sym2 V) := fun s => M.edgeFinset ∩ s.sym2 with hB
  have hterm : ∀ s ∈ parts, (M.induce (↑s : Set V)).edgeFinset.card = (B s).card := by
    intro s hs
    rw [← SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := M) (s := s)]
    rw [SimpleGraph.filter_edgeFinset_toFinset_subset]
  have hnonempty : ∀ e : Sym2 V, e.toFinset.Nonempty := by
    intro e
    induction e using Sym2.ind with
    | _ u v => exact ⟨u, by simp⟩
  have hcoverE : parts.biUnion B = M.edgeFinset := by
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
        have h1 : s(u, v) ∈ M.edgeSet := by simpa [SimpleGraph.edgeFinset] using he
        have hadj' : M.Adj u v := (SimpleGraph.mem_edgeSet M).mp h1
        obtain ⟨s, hsC, hu, hv⟩ := hadj u v hadj'
        refine Finset.mem_biUnion.mpr ⟨s, hsC, ?_⟩
        simp only [hB, Finset.mem_inter]
        refine ⟨he, ?_⟩
        rw [Finset.mem_sym2_iff]
        intro a ha
        rcases Sym2.mem_iff.mp ha with h | h
        · rw [h]; exact hu
        · rw [h]; exact hv
  have hdisjB : ((parts : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint B := by
    intro s hs t ht hst
    change Disjoint (B s) (B t)
    rw [Finset.disjoint_left]
    intro e he he'
    simp only [hB, Finset.mem_inter] at he he'
    rw [Finset.mem_sym2_iff] at he he'
    obtain ⟨a, ha⟩ := hnonempty e
    have ha' : a ∈ e := by rwa [Sym2.mem_toFinset] at ha
    exact (Finset.disjoint_left.mp (hdisjoint s hs t ht hst) (he.2 a ha') (he'.2 a ha'))
  have hcard : M.edgeFinset.card = ∑ s ∈ parts, (B s).card := by
    rw [← hcoverE, Finset.card_biUnion hdisjB]
  have hterm2 : ∀ s ∈ parts, (M.induce (↑s : Set V)).edgeSet.ncard = (B s).card := by
    intro s hs
    rw [← hterm s hs]
    rw [Set.ncard_eq_toFinset_card']
    rfl
  have hEq : M.edgeSet.ncard = ∑ s ∈ parts, (M.induce (↑s : Set V)).edgeSet.ncard := by
    calc M.edgeSet.ncard = M.edgeFinset.card := by
          rw [Set.ncard_eq_toFinset_card']
          rfl
      _ = ∑ s ∈ parts, (B s).card := hcard
      _ = ∑ s ∈ parts, (M.induce (↑s : Set V)).edgeSet.ncard := by
          apply Finset.sum_congr rfl
          intro s hs
          exact (hterm2 s hs).symm
  exact le_of_eq hEq
