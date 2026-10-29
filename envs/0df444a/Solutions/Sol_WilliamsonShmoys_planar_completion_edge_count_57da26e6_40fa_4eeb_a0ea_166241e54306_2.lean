-- Prove2me | solution 2 for WilliamsonShmoys.planar_completion_edge_count_57da26e6_40fa_4eeb_a0ea_166241e54306
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:06:22.155499+00:00
-- url     : https://prove2.me/submissions/8d2772fb-af78-46e8-8f39-61a906a59c11

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex N hV hN
