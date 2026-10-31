-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_014b5904_580f_46f1_bfdb_710877e74ec0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:42:05.468177+00:00
-- url     : https://prove2.me/submissions/d140f21d-e0cb-44a7-bc79-5f72e1bfe243

import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_7f5185ee_24ca_4414_b90e_b6691f6b37ff_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hGconn : G.Connected) (hG : HasPlanarDrawingOn G) : G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.connected_planar_edge_bound__p2m_7f5185ee_24ca_4414_b90e_b6691f6b37ff_a1 G hV hGconn hG
