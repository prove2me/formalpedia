-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_edge_count_upper__p2m_6b45552a_e614_43a1_bcb2_5a02dc98d5fe_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:28:49.514524+00:00
-- url     : https://prove2.me/submissions/6f95b733-a95a-447a-b51e-17b7a7c19540

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound_retry3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_edge_count_bound_retry3 H hDraw hV
