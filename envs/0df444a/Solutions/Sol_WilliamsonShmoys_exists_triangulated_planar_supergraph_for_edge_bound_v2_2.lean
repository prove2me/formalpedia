-- Prove2me | solution 2 for WilliamsonShmoys.exists_triangulated_planar_supergraph_for_edge_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:11:14.828+00:00
-- url     : https://prove2.me/submissions/8545838d-c432-4d47-ad03-610fc6777707

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hPdraw : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V,
      P ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q ∧
        Q.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex P hV hPdraw
