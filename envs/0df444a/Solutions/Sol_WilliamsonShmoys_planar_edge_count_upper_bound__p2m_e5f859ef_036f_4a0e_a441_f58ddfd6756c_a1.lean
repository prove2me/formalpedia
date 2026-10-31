-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_e5f859ef_036f_4a0e_a441_f58ddfd6756c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:22:41.236607+00:00
-- url     : https://prove2.me/submissions/c7d28b97-4f75-4627-8514-4646065033c4

import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_bound_e51c1790

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_graph_edge_bound_e51c1790 L hV hDraw
