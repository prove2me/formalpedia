-- Prove2me | solution 2 for WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_9e9ddd37_2fbe_4f2e_b4a6_63a4b0058d20_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:22:14.656895+00:00
-- url     : https://prove2.me/submissions/a8470e3c-0d18-48c2-8a92-50a5a9478885

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_planar_edge_bound

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound M hM hCard
