-- Prove2me | solution 3 for WilliamsonShmoys.planar_edge_count_upper_of_drawing__p2m_fcb8ec4c_c30d_44dd_a4d8_def1801ee290_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:26:42.179977+00:00
-- url     : https://prove2.me/submissions/876deed1-d50a-4e5b-860d-eafe6f83ec84

import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_edgeSet_ncard_le

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) : H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planarDrawingOn_edgeSet_ncard_le H hCard hH
