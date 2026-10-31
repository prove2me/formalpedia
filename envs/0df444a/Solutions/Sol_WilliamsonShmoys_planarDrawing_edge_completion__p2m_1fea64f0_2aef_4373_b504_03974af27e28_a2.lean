-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_edge_completion__p2m_1fea64f0_2aef_4373_b504_03974af27e28_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:41:13.824973+00:00
-- url     : https://prove2.me/submissions/287ffa9d-6fc0-46b3-b855-86978d322640

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 <= Fintype.card V) : ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_extension G hDraw hV
