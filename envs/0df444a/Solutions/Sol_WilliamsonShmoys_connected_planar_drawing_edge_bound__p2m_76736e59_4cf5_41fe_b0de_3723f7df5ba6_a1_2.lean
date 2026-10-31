-- Prove2me | solution 2 for WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_76736e59_4cf5_41fe_b0de_3723f7df5ba6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:27:57.932985+00:00
-- url     : https://prove2.me/submissions/a228ca8d-1100-4282-9a5f-93c0bdbf455d

import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_a0b92b21_6aa1_495e_a7c5_b4d4c91a44bd

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hConn : H.Connected) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.connected_planar_edge_count_a0b92b21_6aa1_495e_a7c5_b4d4c91a44bd H hConn hDraw hV
