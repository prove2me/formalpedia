-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_maximal_edge_count_completion_aad9569e3b024b25a2de035820e22467
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:29:15.596166+00:00
-- url     : https://prove2.me/submissions/0272a12c-e0ec-4f60-b1d1-b427a32c8312

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        H.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex K hV hK
