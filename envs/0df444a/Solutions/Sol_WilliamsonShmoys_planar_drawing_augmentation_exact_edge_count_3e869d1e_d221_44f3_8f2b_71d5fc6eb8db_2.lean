-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_augmentation_exact_edge_count_3e869d1e_d221_44f3_8f2b_71d5fc6eb8db
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:26:28.270014+00:00
-- url     : https://prove2.me/submissions/827be0f8-fa9c-4197-a5e2-f66ca7ef5333

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex G hV hG
