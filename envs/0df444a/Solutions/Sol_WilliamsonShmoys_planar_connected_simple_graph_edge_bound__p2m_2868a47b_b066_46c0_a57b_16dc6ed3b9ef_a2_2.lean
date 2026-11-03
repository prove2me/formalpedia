-- Prove2me | solution 2 for WilliamsonShmoys.planar_connected_simple_graph_edge_bound__p2m_2868a47b_b066_46c0_a57b_16dc6ed3b9ef_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:45:20.390797+00:00
-- url     : https://prove2.me/submissions/59eeafb3-e9fb-4d7f-8f32-a2d6dcaf70cf

import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_connected_edge_bound__p2m_b11eb619_37a3_43a5_a612_72f4475984ba_a2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : HasPlanarDrawingOn G) (hcard : 3 ≤ Fintype.card V) (hconn : G.Connected) : G.edgeFinset.card + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_simple_graph_connected_edge_bound__p2m_b11eb619_37a3_43a5_a612_72f4475984ba_a2 G hG hcard hconn