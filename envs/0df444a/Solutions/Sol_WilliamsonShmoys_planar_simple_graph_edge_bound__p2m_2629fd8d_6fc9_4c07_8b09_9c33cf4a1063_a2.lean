-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_2629fd8d_6fc9_4c07_8b09_9c33cf4a1063_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:08:48.771+00:00
-- url     : https://prove2.me/submissions/30aa9b65-2ce8-43cb-be1c-c5bd7f7a324c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_connected_edge_bound__p2m_b11eb619_37a3_43a5_a612_72f4475984ba_a2
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_disconnected_edge_bound__p2m_b11eb619_37a3_43a5_a612_72f4475984ba_a2
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) : G.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  by_cases hconn : G.Connected
  · exact WilliamsonShmoys.planar_simple_graph_connected_edge_bound__p2m_b11eb619_37a3_43a5_a612_72f4475984ba_a2
      G hG hcard hconn
  · exact WilliamsonShmoys.planar_simple_graph_disconnected_edge_bound__p2m_b11eb619_37a3_43a5_a612_72f4475984ba_a2
      G hG hcard hconn