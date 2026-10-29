-- Prove2me | solution 2 for WilliamsonShmoys.exists_planar_euler_edge_count_completion
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:11:46.816002+00:00
-- url     : https://prove2.me/submissions/6f7ed3d9-9d15-4447-92e4-07c055f0f8ac

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ J : SimpleGraph V,
      H ≤ J ∧
      WilliamsonShmoys.HasPlanarDrawingOn J ∧
      J.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex H hV hH
