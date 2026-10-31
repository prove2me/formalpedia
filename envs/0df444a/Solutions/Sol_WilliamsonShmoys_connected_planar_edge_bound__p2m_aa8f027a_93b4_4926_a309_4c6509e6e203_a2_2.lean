-- Prove2me | solution 2 for WilliamsonShmoys.connected_planar_edge_bound__p2m_aa8f027a_93b4_4926_a309_4c6509e6e203_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:13:52.413245+00:00
-- url     : https://prove2.me/submissions/068f940d-cc16-4b52-986c-654c7ea4104d

import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_a0b92b21_6aa1_495e_a7c5_b4d4c91a44bd

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hConnected : H.Connected) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.connected_planar_edge_count_a0b92b21_6aa1_495e_a7c5_b4d4c91a44bd H hConnected hDraw hV
