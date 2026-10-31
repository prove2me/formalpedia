-- Prove2me | solution 3 for WilliamsonShmoys.planar_edge_upper_bound__p2m_43e5ee36_822f_4bf9_b718_27a0868cee65_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:16:37.039705+00:00
-- url     : https://prove2.me/submissions/4aabd6d8-4e36-4d66-8edb-32ce2e697635

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound_retry3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_edge_count_bound_retry3 H hDraw hV
