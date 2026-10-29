-- Prove2me | solution 2 for WilliamsonShmoys.exists_drawable_triangulated_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:15:25.333757+00:00
-- url     : https://prove2.me/submissions/60744a70-f5d5-46fd-8f17-c9619d630543

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex L hV hL
