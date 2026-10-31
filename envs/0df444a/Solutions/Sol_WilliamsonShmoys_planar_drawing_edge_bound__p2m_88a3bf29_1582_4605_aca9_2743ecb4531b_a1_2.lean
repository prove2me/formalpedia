-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_88a3bf29_1582_4605_aca9_2743ecb4531b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T20:59:40.371594+00:00
-- url     : https://prove2.me/submissions/cc9235fd-d56b-4432-b1a5-d7be17b25b66

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound_retry3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 ≤ Fintype.card V) : G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_edge_count_bound_retry3 G hDraw hV
