-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_98c8bf31_da7f_4753_99f2_642509315647_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:41:07.388005+00:00
-- url     : https://prove2.me/submissions/7c53d50f-b9c0-4cb9-bde5-630967db5f4b

import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_bound_e51c1790

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_graph_edge_bound_e51c1790 G hV hG
