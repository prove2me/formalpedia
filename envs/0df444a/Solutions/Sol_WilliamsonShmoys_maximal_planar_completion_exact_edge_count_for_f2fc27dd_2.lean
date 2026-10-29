-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_completion_exact_edge_count_for_f2fc27dd
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:06:21.480998+00:00
-- url     : https://prove2.me/submissions/9987ce55-dbc6-454b-8f81-8f2d2e1e6254

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
