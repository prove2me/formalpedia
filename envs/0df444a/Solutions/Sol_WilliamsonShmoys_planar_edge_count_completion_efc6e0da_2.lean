-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_count_completion_efc6e0da
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:16:49.247505+00:00
-- url     : https://prove2.me/submissions/a6fd2355-4b8b-4929-9cf3-36bc3826ac6f

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ J : SimpleGraph V,
      G ≤ J ∧
      WilliamsonShmoys.HasPlanarDrawingOn J ∧
      J.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex G hV hG
