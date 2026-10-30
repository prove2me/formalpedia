-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_from_connected_induced__p2m_66ade5d4_3842_4532_bbd5_36e43a15d1f5_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:51:38.578243+00:00
-- url     : https://prove2.me/submissions/e4834a05-96f7-4a3d-acf0-64faa47a6e38
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_component_partition_local_bounds__p2m_6acb2709_a7d1_4f30_86cb_5088257eb588_a2
import Theorems.Thm_WilliamsonShmoys_sum_local_bounds__p2m_6acb2709_a7d1_4f30_86cb_5088257eb588_a2

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hBound : ∀ (s : Finset V),
      (H.induce (↑s : Set V)).Connected →
      3 ≤ Fintype.card {v // v ∈ s} →
      (H.induce (↑s : Set V)).edgeSet.ncard + 6 ≤
        3 * Fintype.card {v // v ∈ s}) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨parts, hCardSum, hEdgeSum, hLocal⟩ :=
    WilliamsonShmoys.connected_component_partition_local_bounds__p2m_6acb2709_a7d1_4f30_86cb_5088257eb588_a2
      H hBound
  exact WilliamsonShmoys.sum_local_bounds__p2m_6acb2709_a7d1_4f30_86cb_5088257eb588_a2
    H hCard parts hCardSum hEdgeSum hLocal