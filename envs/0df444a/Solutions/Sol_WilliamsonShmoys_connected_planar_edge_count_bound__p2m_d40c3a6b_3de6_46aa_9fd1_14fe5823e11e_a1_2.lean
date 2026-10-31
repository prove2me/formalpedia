-- Prove2me | solution 2 for WilliamsonShmoys.connected_planar_edge_count_bound__p2m_d40c3a6b_3de6_46aa_9fd1_14fe5823e11e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T20:59:40.439114+00:00
-- url     : https://prove2.me/submissions/963b16d7-8b06-4864-92f9-81f35d483988

import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_upper_bound_c3c27980_9f1d_4b26_ac26_4100a7115914

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hHconn : H.Connected) (hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H) : H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.connected_planar_edge_upper_bound_c3c27980_9f1d_4b26_ac26_4100a7115914 H hV hHconn hHplanar
