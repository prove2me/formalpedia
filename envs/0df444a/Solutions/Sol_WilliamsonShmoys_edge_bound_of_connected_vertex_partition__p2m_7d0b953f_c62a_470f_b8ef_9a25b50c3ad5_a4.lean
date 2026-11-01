-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_of_connected_vertex_partition__p2m_7d0b953f_c62a_470f_b8ef_9a25b50c3ad5_a4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:03:14.026985+00:00
-- url     : https://prove2.me/submissions/9650f0a0-0cfa-4237-bcea-4164c2a0869c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_partition_edge_sum_bound__p2m_6c5365e9_a8ca_483d_a274_7738f7675557_a1
import Theorems.Thm_WilliamsonShmoys_partition_size_sum_bound__p2m_6c5365e9_a8ca_483d_a274_7738f7675557_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hlocal : ∀ (s : Finset V),
      (K.induce (↑s : Set V)).Connected →
      (letI : DecidableRel (K.induce (↑s : Set V)).Adj := Classical.decRel _;
       (K.induce (↑s : Set V)).edgeFinset.card <=
         max 1 (3 * Fintype.card s - 6)))
    (parts : Finset (Finset V))
    (hparts :
      (∀ s ∈ parts, s.Nonempty ∧ (K.induce (↑s : Set V)).Connected) ∧
      (∀ v, ∃ s ∈ parts, v ∈ s) ∧
      (∀ s ∈ parts, ∀ t ∈ parts, s ≠ t → Disjoint s t) ∧
      (∀ u v, K.Adj u v → ∃ s ∈ parts, u ∈ s ∧ v ∈ s)) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
     K.edgeFinset.card <= 3 * Fintype.card V - 6) := by
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  have hsum :=
    WilliamsonShmoys.partition_edge_sum_bound__p2m_6c5365e9_a8ca_483d_a274_7738f7675557_a1
      K hlocal parts hparts
  have hsize :=
    WilliamsonShmoys.partition_size_sum_bound__p2m_6c5365e9_a8ca_483d_a274_7738f7675557_a1
      (V := V) hcard K parts hparts
  change K.edgeFinset.card <= 3 * Fintype.card V - 6
  exact le_trans hsum hsize