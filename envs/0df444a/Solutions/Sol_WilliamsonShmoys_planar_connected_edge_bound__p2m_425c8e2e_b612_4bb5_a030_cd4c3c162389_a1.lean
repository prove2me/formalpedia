-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_edge_bound__p2m_425c8e2e_b612_4bb5_a030_cd4c3c162389_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:44:51.751909+00:00
-- url     : https://prove2.me/submissions/bbd9049e-4dfd-44be-8d66-f7c451018e1e

import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_bound__p2m_e46e8dd0_1680_4d93_a7d5_10e0bd7d8348_a4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hConn : H.Connected) (hV : 3 ≤ Fintype.card V) : H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.connected_planar_edge_count_bound__p2m_e46e8dd0_1680_4d93_a7d5_10e0bd7d8348_a4 H hDraw hConn hV
