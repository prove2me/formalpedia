-- Prove2me | solution 2 for WilliamsonShmoys.planar_completion_at_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:06:23.857998+00:00
-- url     : https://prove2.me/submissions/cd6d45fa-a2d5-46df-8710-62783be2449a

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex M hV hM
