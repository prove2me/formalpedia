-- Prove2me | solution 3 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_76a86dc1_411a_4f86_8755_ab6ac02ce22d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:24:54.502991+00:00
-- url     : https://prove2.me/submissions/fe1cd809-4241-4fa5-a7ee-9199e03d6f79

import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_edgeSet_ncard_le

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) : T.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planarDrawingOn_edgeSet_ncard_le T hV hT
