-- Prove2me | solution 1 for WilliamsonShmoys.partition_edge_partition_card__p2m_dcaefdba_b10e_4220_bda1_55f53e9c0d30_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:13:13.000336+00:00
-- url     : https://prove2.me/submissions/9fc77d4b-1295-4b0b-8549-48607340693a

import Mathlib
import Theorems.Thm_WilliamsonShmoys_partition_edge_partition_card_filter__p2m_ace44350_7233_4698_89fd_6ad5d167961d_a3

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (parts : Finset (Finset V))
    (hdisj : ∀ s ∈ parts, ∀ t ∈ parts, s ≠ t -> Disjoint s t)
    (hcontain : ∀ u v, K.Adj u v -> ∃ s ∈ parts, u ∈ s ∧ v ∈ s) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      K.edgeFinset.card = ∑ s ∈ parts, (K.induce (↑s : Set V)).edgeFinset.card) := by
  classical
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  change K.edgeFinset.card = ∑ s ∈ parts, (K.induce (↑s : Set V)).edgeFinset.card
  rw [WilliamsonShmoys.partition_edge_partition_card_filter__p2m_ace44350_7233_4698_89fd_6ad5d167961d_a3 K parts hdisj hcontain]
  apply Finset.sum_congr rfl
  intro s hs
  exact SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := K) s