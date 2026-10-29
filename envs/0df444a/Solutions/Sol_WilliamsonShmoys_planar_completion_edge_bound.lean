-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:21:11.554452+00:00
-- url     : https://prove2.me/submissions/1a6fe920-f8ad-4acc-afff-c2d3236db83b

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ K : SimpleGraph V,
      J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex J hV hJ
