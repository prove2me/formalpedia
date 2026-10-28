-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_edge_count_upper_bound__p2m_03ab0e36_fd73_4929_a651_a82d3a3cc822_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:20:28.702953+00:00
-- url     : https://prove2.me/submissions/072ccc42-b1d8-4f98-a96c-5e809062e96c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_connected_augmentation__p2m_7f5185ee_24ca_4414_b90e_b6691f6b37ff_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_7f5185ee_24ca_4414_b90e_b6691f6b37ff_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨N, hEdges, hConnected, hDrawing⟩ :=
    WilliamsonShmoys.planarDrawingOn_connected_augmentation__p2m_7f5185ee_24ca_4414_b90e_b6691f6b37ff_a1
      M hM
  have hN :=
    WilliamsonShmoys.connected_planar_edge_bound__p2m_7f5185ee_24ca_4414_b90e_b6691f6b37ff_a1
      N hV hConnected hDrawing
  exact (Set.ncard_mono hEdges).trans hN

