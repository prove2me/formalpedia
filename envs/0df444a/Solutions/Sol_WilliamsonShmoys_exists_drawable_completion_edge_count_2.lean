-- Prove2me | solution 2 for WilliamsonShmoys.exists_drawable_completion_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:17:21.288997+00:00
-- url     : https://prove2.me/submissions/e3a46cab-a7d2-42da-a532-f533b36a0d40

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ H : SimpleGraph V, N ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex N hV hN
