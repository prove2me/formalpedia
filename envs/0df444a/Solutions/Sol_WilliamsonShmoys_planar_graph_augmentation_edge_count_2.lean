-- Prove2me | solution 2 for WilliamsonShmoys.planar_graph_augmentation_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:25:04.429442+00:00
-- url     : https://prove2.me/submissions/18f9282e-b986-4c43-a614-5798e79abfe0

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hLplanar : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        M.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex L hV hLplanar
