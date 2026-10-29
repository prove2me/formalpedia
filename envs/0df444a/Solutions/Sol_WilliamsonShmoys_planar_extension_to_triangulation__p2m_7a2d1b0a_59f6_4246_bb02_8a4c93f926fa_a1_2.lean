-- Prove2me | solution 2 for WilliamsonShmoys.planar_extension_to_triangulation__p2m_7a2d1b0a_59f6_4246_bb02_8a4c93f926fa_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:31:00.16727+00:00
-- url     : https://prove2.me/submissions/92a6bf4a-bd1f-43e2-8135-e51d2a9a7c96

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ M : SimpleGraph V, G ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ M.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex G hCard hDraw
