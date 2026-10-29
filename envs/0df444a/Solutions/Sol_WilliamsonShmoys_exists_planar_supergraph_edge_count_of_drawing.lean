-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_edge_count_of_drawing
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:25:46.420394+00:00
-- url     : https://prove2.me/submissions/1c955635-91bf-446c-a9a7-708d9d3d0cfb

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex M hV hM
