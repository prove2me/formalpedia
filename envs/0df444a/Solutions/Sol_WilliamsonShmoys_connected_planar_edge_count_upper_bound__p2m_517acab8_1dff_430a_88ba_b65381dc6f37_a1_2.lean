-- Prove2me | solution 2 for WilliamsonShmoys.connected_planar_edge_count_upper_bound__p2m_517acab8_1dff_430a_88ba_b65381dc6f37_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:00:15.887997+00:00
-- url     : https://prove2.me/submissions/c34495ff-1ebe-464f-863b-34ec7c691fe4

import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_a0b92b21_6aa1_495e_a7c5_b4d4c91a44bd

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (Z : SimpleGraph V) (hconn : Z.Connected) (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z) (hV : 3 ≤ Fintype.card V) : Z.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.connected_planar_edge_count_a0b92b21_6aa1_495e_a7c5_b4d4c91a44bd Z hconn hZ hV
