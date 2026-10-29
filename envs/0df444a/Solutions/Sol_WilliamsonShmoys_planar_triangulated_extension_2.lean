-- Prove2me | solution 2 for WilliamsonShmoys.planar_triangulated_extension
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:14:22.896991+00:00
-- url     : https://prove2.me/submissions/2285c2a0-0d6a-4a3d-8686-1e3b18da5640

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        M.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex L hV hL
