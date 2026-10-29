-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_has_triangulation_extension_for_edge_bound_c61b3391
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:22:03.916988+00:00
-- url     : https://prove2.me/submissions/a43f2c6f-5450-4b80-b3a2-356de1f2b7af

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex H hV hH
