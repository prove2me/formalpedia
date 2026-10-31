-- Prove2me | solution 2 for WilliamsonShmoys.connected_planar_edge_count_upper_bound__p2m_bfc81ce3_c50f_433a_ae04_d243cae0dc3b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:13:59.122252+00:00
-- url     : https://prove2.me/submissions/c5d7029e-35e1-4d7d-824e-60495c560ced

import Theorems.Thm_WilliamsonShmoys_planar_edgeSet_ncard_le

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) (hconn : T.Connected) : T.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_edgeSet_ncard_le T hV hT hconn
