-- Prove2me | solution 2 for WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_94c3c327_8601_4c2d_adbc_08897459bc6e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:22:51.812925+00:00
-- url     : https://prove2.me/submissions/283c2f4b-0046-4b00-8ce2-da90d4429f94

import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_repair3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_edge_upper_bound_repair3 G hV hG
