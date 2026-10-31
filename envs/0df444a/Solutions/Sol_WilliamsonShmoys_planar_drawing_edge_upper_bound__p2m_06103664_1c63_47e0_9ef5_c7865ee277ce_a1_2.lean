-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_06103664_1c63_47e0_9ef5_c7865ee277ce_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:54:11.254428+00:00
-- url     : https://prove2.me/submissions/bdf3d392-1579-4ba6-9a76-df2793450269

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound_retry3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_edge_count_bound_retry3 H hDraw hV
