-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_7faa0883_91bf_4801_b0cf_9d9827720e15_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:01:04.540004+00:00
-- url     : https://prove2.me/submissions/d5fb1357-38b4-4e79-bf9f-5e6bf08fe762

import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_repair3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : HasPlanarDrawingOn L) : L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_edge_upper_bound_repair3 L hV hDraw
