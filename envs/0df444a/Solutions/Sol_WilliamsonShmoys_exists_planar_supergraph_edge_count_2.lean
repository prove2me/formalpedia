-- Prove2me | solution 2 for WilliamsonShmoys.exists_planar_supergraph_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:24:22.278449+00:00
-- url     : https://prove2.me/submissions/57a33148-0480-4204-8859-ce40409060cd

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ H : SimpleGraph V,
      M ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex M hV hM
