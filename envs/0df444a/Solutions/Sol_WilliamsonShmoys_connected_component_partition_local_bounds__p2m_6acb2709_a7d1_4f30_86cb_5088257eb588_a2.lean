-- Prove2me | solution 1 for WilliamsonShmoys.connected_component_partition_local_bounds__p2m_6acb2709_a7d1_4f30_86cb_5088257eb588_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:05:05.617415+00:00
-- url     : https://prove2.me/submissions/f107f629-aba1-4c0c-bfb7-c1c60a38c8d3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_component_partition_decomposition__p2m_ac4d32fd_da9a_4d4d_92cd_7d05f79f270c_a1
import Theorems.Thm_WilliamsonShmoys_connected_component_partition_local_bound__p2m_ac4d32fd_da9a_4d4d_92cd_7d05f79f270c_a1

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hBound : ∀ (s : Finset V),
      (H.induce (↑s : Set V)).Connected →
      3 ≤ Fintype.card {v // v ∈ s} →
      (H.induce (↑s : Set V)).edgeSet.ncard + 6 ≤ 3 * Fintype.card {v // v ∈ s}) :
    ∃ (parts : Finset (Finset V)),
      (∑ s ∈ parts, Fintype.card {v // v ∈ s}) = Fintype.card V ∧
      (∑ s ∈ parts, (H.induce (↑s : Set V)).edgeSet.ncard) = H.edgeSet.ncard ∧
      ∀ s ∈ parts,
        1 ≤ Fintype.card {v // v ∈ s} ∧
        (H.induce (↑s : Set V)).Connected ∧
        (H.induce (↑s : Set V)).edgeSet.ncard +
          (if 3 ≤ Fintype.card {v // v ∈ s} then 6 else 3) ≤
            3 * Fintype.card {v // v ∈ s} := by
  obtain ⟨parts, hVertices, hEdges, hParts⟩ :=
    WilliamsonShmoys.connected_component_partition_decomposition__p2m_ac4d32fd_da9a_4d4d_92cd_7d05f79f270c_a1 H
  refine ⟨parts, hVertices, hEdges, ?_⟩
  intro s hs
  obtain ⟨hNonempty, hConnected⟩ := hParts s hs
  exact ⟨hNonempty, hConnected,
    WilliamsonShmoys.connected_component_partition_local_bound__p2m_ac4d32fd_da9a_4d4d_92cd_7d05f79f270c_a1 H hBound s hNonempty hConnected⟩