-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_triangulation_completion_on_same_vertices
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:20:29.766713+00:00
-- url     : https://prove2.me/submissions/0db02bef-2631-46e8-acbf-2ca3425c0a78

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex H hV hHdraw
