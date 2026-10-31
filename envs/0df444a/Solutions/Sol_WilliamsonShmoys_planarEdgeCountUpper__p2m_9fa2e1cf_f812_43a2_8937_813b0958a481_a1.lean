-- Prove2me | solution 1 for WilliamsonShmoys.planarEdgeCountUpper__p2m_9fa2e1cf_f812_43a2_8937_813b0958a481_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:41:40.590808+00:00
-- url     : https://prove2.me/submissions/ca8f0aeb-dd98-4e32-97f4-d9c27f36a454

import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_repair3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : HasPlanarDrawingOn N) : N.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_edge_upper_bound_repair3 N hV hDraw
