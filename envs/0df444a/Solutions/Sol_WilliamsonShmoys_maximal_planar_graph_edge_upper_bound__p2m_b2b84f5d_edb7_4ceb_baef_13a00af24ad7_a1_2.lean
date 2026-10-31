-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_graph_edge_upper_bound__p2m_b2b84f5d_edb7_4ceb_baef_13a00af24ad7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:22:06.726899+00:00
-- url     : https://prove2.me/submissions/f0e8526e-a546-49c5-8860-92a98ba0dc7f

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_planar_edge_bound

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V) (hDraw : HasPlanarDrawingOn R) (hV : 3 ≤ Fintype.card V) : R.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound R hDraw hV
