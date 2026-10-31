-- Prove2me | solution 2 for WilliamsonShmoys.connected_drawable_edge_bound__p2m_2c5adea4_d505_4326_974e_37a0f04a34d9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:45:00.925394+00:00
-- url     : https://prove2.me/submissions/5bc9c37c-72bb-406c-a0eb-fa31f8c1fcd8

import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound_from_embedding

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hConn : H.Connected) (hDraw : HasPlanarDrawingOn H) (hCard : 3 ≤ Fintype.card V) : H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.connected_planar_drawing_edge_bound_from_embedding H hConn hDraw hCard
