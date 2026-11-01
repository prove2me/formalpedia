-- Prove2me | solution 1 for WilliamsonShmoys.partition_edge_partition_card_filter__p2m_ace44350_7233_4698_89fd_6ad5d167961d_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:20:10.083928+00:00
-- url     : https://prove2.me/submissions/4e121298-5618-4a26-b63a-c43cf32b9cec

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (parts : Finset (Finset V))
    (hdisj : ∀ s ∈ parts, ∀ t ∈ parts, s ≠ t → Disjoint s t)
    (hcontain : ∀ u v, K.Adj u v → ∃ s ∈ parts, u ∈ s ∧ v ∈ s) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      K.edgeFinset.card =
        ∑ s ∈ parts, (K.edgeFinset.filter (fun e => e.toFinset ⊆ s)).card) := by
  classical
  let r : Sym2 V → Finset V → Prop := fun e s => e.toFinset ⊆ s
  have hone (e : Sym2 V) (he : e ∈ K.edgeFinset) :
      (parts.filter (fun s => r e s)).card = 1 := by
    induction e using Sym2.inductionOn with
    | hf u v =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      obtain ⟨s, hs, hus, hvs⟩ := hcontain u v he
      have hsub : (s(u, v)).toFinset ⊆ s := by
        rw [Sym2.toFinset_mk_eq]
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hxu | hxv
        · simpa [hxu] using hus
        · simpa [hxv] using hvs
      have hfilter :
          parts.filter (fun t => (s(u, v)).toFinset ⊆ t) = {s} := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨ht, hts⟩
          by_contra hne
          have hd := hdisj s hs t ht (Ne.symm hne)
          have hu_t : u ∈ t := hts (by simp [Sym2.toFinset_mk_eq])
          exact (Finset.disjoint_left.mp hd) hus hu_t
        · intro hts
          subst t
          exact ⟨hs, hsub⟩
      simpa [r, hfilter]
  have hdc :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := K.edgeFinset) (t := parts) (r := r)
  calc
    K.edgeFinset.card =
        ∑ e ∈ K.edgeFinset, (parts.filter (fun s => r e s)).card := by
          symm
          calc
            _ = ∑ e ∈ K.edgeFinset, 1 := by
              apply Finset.sum_congr rfl
              intro e he
              exact hone e he
            _ = K.edgeFinset.card := by simp
    _ = ∑ s ∈ parts, (K.edgeFinset.filter (fun e => r e s)).card := by
          simpa [Finset.bipartiteAbove, Finset.bipartiteBelow] using hdc
    _ = ∑ s ∈ parts, (K.edgeFinset.filter (fun e => e.toFinset ⊆ s)).card := by
          rfl
