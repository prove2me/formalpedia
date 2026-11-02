-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_0a96650e_3562_4e4d_ac7d_bc404fba85ef_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:04:59.743942+00:00
-- url     : https://prove2.me/submissions/2d80d43d-4458-4609-9266-4ca45de9330c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_25b88d59_9c9b_4413_bef8_c3d95089e4b3_a3
import Theorems.Thm_WilliamsonShmoys_disconnected_planar_edge_bound__p2m_25b88d59_9c9b_4413_bef8_c3d95089e4b3_a3
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     N.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  by_cases hconn : N.Connected
  · exact WilliamsonShmoys.connected_planar_edge_bound__p2m_25b88d59_9c9b_4413_bef8_c3d95089e4b3_a3
      N hcard hN hconn
  · exact WilliamsonShmoys.disconnected_planar_edge_bound__p2m_25b88d59_9c9b_4413_bef8_c3d95089e4b3_a3
      N hcard hN hconn