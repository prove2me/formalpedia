-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_edge_count_triangulation_extension_3daebd93
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:34:08.875991+00:00
-- url     : https://prove2.me/submissions/ab0e8199-484e-4fcc-a494-66de703cef55

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex H hV hH
