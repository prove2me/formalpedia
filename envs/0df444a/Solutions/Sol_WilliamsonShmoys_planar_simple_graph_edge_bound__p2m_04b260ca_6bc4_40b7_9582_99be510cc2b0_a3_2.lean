-- Prove2me | solution 2 for WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_04b260ca_6bc4_40b7_9582_99be510cc2b0_a3
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:11:16.338645+00:00
-- url     : https://prove2.me/submissions/f3cee79e-cb0f-47e1-ba2a-2decf38ad62d

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound__p2m_37c28fdb_a658_40e3_b030_60d915d37051_a2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_count_bound__p2m_37c28fdb_a658_40e3_b030_60d915d37051_a2 G hG hcard
