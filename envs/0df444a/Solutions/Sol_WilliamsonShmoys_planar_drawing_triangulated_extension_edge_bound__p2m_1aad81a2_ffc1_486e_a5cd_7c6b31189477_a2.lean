-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulated_extension_edge_bound__p2m_1aad81a2_ffc1_486e_a5cd_7c6b31189477_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T02:26:09.900986+00:00
-- url     : https://prove2.me/submissions/681b3fb8-e6f6-4b85-b908-eeeaf4840444

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_drawable_extension__p2m_bb4dce47_9275_45c5_899b_6355cecbb075_a5
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_bb4dce47_9275_45c5_899b_6355cecbb075_a5

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hconn : G.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Connected ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hGH, hHdraw, hHconn, hCardle, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_drawable_extension__p2m_bb4dce47_9275_45c5_899b_6355cecbb075_a5
      G hconn hdraw hCard
  have hEdgeCount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_bb4dce47_9275_45c5_899b_6355cecbb075_a5
      H hHconn hHdraw hCard hmax
  exact ⟨H, hGH, hHdraw, hHconn, hCardle, hEdgeCount⟩
