-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_triangulation_extension_818be957_e7c4_4eb2_84ce_f98ac89fa6a9
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:22:56.218551+00:00
-- url     : https://prove2.me/submissions/1ed4b1da-074c-4d8f-a81f-4a9e9799cf09

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ P : SimpleGraph V,
      G ≤ P ∧ WilliamsonShmoys.HasPlanarDrawingOn P ∧
        P.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex G hV hG
