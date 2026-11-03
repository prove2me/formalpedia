-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_438c2037_6b64_401b_a3fa_84e1ccf42d6c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:52:45.808906+00:00
-- url     : https://prove2.me/submissions/8d5d636b-cc4f-4fd1-86ed-fa4c56fe03db

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_0d2111fe_49a0_4983_b8b9_46fbb1acc127_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_count_upper_bound__p2m_0d2111fe_49a0_4983_b8b9_46fbb1acc127_a1 G hG hcard