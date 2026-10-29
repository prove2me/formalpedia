-- Prove2me | solution 2 for WilliamsonShmoys.planar_supergraph_completion_exact_edge_count__p2m_c3a9b232_8896_4daf_b121_720ec89c3bee_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:23:40.158716+00:00
-- url     : https://prove2.me/submissions/c22dae30-ebd5-486f-b8d5-e22eb63d537b

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    exists H : SimpleGraph V,
      G <= H /\ WilliamsonShmoys.HasPlanarDrawingOn H /\
        H.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex G hV hG
