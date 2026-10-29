-- Prove2me | solution 2 for WilliamsonShmoys.planar_triangulation_completion
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:27:51.777987+00:00
-- url     : https://prove2.me/submissions/d4bcfc47-a2d9-4a6e-8c38-f48d16697766

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M <= N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex M hV hM
