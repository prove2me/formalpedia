-- Prove2me | solution 2 for WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_84c43119_f87e_4738_abb0_0796ef4e5b94_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:43:55.300999+00:00
-- url     : https://prove2.me/submissions/a01ffcbd-4d27-476c-8404-2694ad614376

import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_upper_bound_c3c27980_9f1d_4b26_ac26_4100a7115914

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hConn : G.Connected) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.connected_planar_edge_upper_bound_c3c27980_9f1d_4b26_ac26_4100a7115914 G hCard hConn hG
