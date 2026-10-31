-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_edge_completion__p2m_09fd82f6_9481_4fe8_ab66_93ef18097a0d_a5
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:38:00.679465+00:00
-- url     : https://prove2.me/submissions/fb05ad44-998d-41ab-a0f6-ec760284a785

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_v2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_completion_v2 G hDraw hCard
