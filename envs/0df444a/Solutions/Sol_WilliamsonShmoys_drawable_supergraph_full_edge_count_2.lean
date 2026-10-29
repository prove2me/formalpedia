-- Prove2me | solution 2 for WilliamsonShmoys.drawable_supergraph_full_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:29:57.527997+00:00
-- url     : https://prove2.me/submissions/292d726f-4c02-4abd-836a-b49ba606d91d

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        M.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex L hV hL
