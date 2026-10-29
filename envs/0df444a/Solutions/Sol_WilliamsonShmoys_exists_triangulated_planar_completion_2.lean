-- Prove2me | solution 2 for WilliamsonShmoys.exists_triangulated_planar_completion
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:18:13.647993+00:00
-- url     : https://prove2.me/submissions/1df332f7-62f8-4e7f-aec8-cdf4231369c0

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex G hV hG
