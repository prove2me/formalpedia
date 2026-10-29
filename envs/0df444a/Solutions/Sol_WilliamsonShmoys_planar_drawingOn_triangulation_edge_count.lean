-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_triangulation_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:19:47.89801+00:00
-- url     : https://prove2.me/submissions/3371e9ca-f186-44e4-bdce-6ac42d3e8ea3

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V, P ≤ Q ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      Q.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex P hV hP
