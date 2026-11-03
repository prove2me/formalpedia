-- Prove2me | solution 2 for WilliamsonShmoys.connected_planar_edge_upper_bound__p2m_ee19bce3_aed2_4043_9cb4_9bf993438165_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:43:37.296004+00:00
-- url     : https://prove2.me/submissions/d38030a5-6e76-4108-a38e-6bfc39907ffc

import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_e37f737c_f285_4a30_83a0_16b070403a61_a2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hconn : G.Connected) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     G.edgeFinset.card ≤ 3 * Fintype.card V - 6) :=
  WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_e37f737c_f285_4a30_83a0_16b070403a61_a2 G hG hV