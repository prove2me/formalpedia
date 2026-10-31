-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound__p2m_7f8156d0_59cd_483d_b914_1d18d842c166_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T11:49:04.777633+00:00
-- url     : https://prove2.me/submissions/621284f9-b0ba-4d46-a802-d5b8414a0601

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_for_edge_count__p2m_2a72d934_5721_47e6_9f14_7bb2bf8ff8c2_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_2a72d934_5721_47e6_9f14_7bb2bf8ff8c2_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨L, hSub, hDraw, hCount, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_count__p2m_2a72d934_5721_47e6_9f14_7bb2bf8ff8c2_a2
      G hG
  have hExact :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_2a72d934_5721_47e6_9f14_7bb2bf8ff8c2_a2
      L hV hDraw hMax
  omega