-- Prove2me | solution 1 for WilliamsonShmoys.partition_edge_sum_bound__p2m_6c5365e9_a8ca_483d_a274_7738f7675557_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:07:27.060958+00:00
-- url     : https://prove2.me/submissions/86ee245e-ae46-449f-b118-e3eb7209c5e7

import Mathlib
import Theorems.Thm_WilliamsonShmoys_partition_edge_partition_card__p2m_dcaefdba_b10e_4220_bda1_55f53e9c0d30_a1
import Theorems.Thm_WilliamsonShmoys_partition_edge_local_sharp_bound__p2m_dcaefdba_b10e_4220_bda1_55f53e9c0d30_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hlocal : ∀ (s : Finset V), (K.induce (↑s : Set V)).Connected →
      (letI : DecidableRel (K.induce (↑s : Set V)).Adj := Classical.decRel _;
       (K.induce (↑s : Set V)).edgeFinset.card ≤ max 1 (3 * Fintype.card s - 6)))
    (parts : Finset (Finset V))
    (hparts : (∀ s ∈ parts, s.Nonempty ∧ (K.induce (↑s : Set V)).Connected) ∧
      (∀ v, ∃ s ∈ parts, v ∈ s) ∧
      (∀ s ∈ parts, ∀ t ∈ parts, s ≠ t → Disjoint s t) ∧
      (∀ u v, K.Adj u v → ∃ s ∈ parts, u ∈ s ∧ v ∈ s)) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
     let f : Finset V → Nat := fun s =>
       if Fintype.card s ≤ 1 then 0 else if Fintype.card s = 2 then 1 else 3 * Fintype.card s - 6;
     K.edgeFinset.card ≤ ∑ s ∈ parts, f s) := by
  classical
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  let f : Finset V → Nat := fun s =>
    if Fintype.card s ≤ 1 then 0 else if Fintype.card s = 2 then 1 else 3 * Fintype.card s - 6
  change K.edgeFinset.card ≤ ∑ s ∈ parts, f s
  calc
    K.edgeFinset.card = ∑ s ∈ parts, (K.induce (↑s : Set V)).edgeFinset.card :=
      WilliamsonShmoys.partition_edge_partition_card__p2m_dcaefdba_b10e_4220_bda1_55f53e9c0d30_a1
        K parts hparts.2.2.1 hparts.2.2.2
    _ ≤ ∑ s ∈ parts, f s := by
      apply Finset.sum_le_sum
      intro s hs
      exact WilliamsonShmoys.partition_edge_local_sharp_bound__p2m_dcaefdba_b10e_4220_bda1_55f53e9c0d30_a1
        K hlocal parts s hs (hparts.1 s hs)