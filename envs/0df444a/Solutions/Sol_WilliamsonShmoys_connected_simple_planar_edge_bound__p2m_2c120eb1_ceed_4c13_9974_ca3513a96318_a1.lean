-- Prove2me | solution 1 for WilliamsonShmoys.connected_simple_planar_edge_bound__p2m_2c120eb1_ceed_4c13_9974_ca3513a96318_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:49:01.474103+00:00
-- url     : https://prove2.me/submissions/a6a7911b-ab1a-4db2-8699-efce76a7dfbb

import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound_from_embedding

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hConn : H.Connected) (hDraw : HasPlanarDrawingOn H) (hCard : 3 <= Fintype.card V) : H.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
  WilliamsonShmoys.connected_planar_drawing_edge_bound_from_embedding H hConn hDraw hCard
