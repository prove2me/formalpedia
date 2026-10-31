-- Prove2me | solution 2 for WilliamsonShmoys.planar_connected_edge_bound__p2m_4414481d_333a_4f96_8a2d_2d6fda1fe3c0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:53:52.65298+00:00
-- url     : https://prove2.me/submissions/08e3ffc9-30f3-4489-86fd-a50f8a8f0c0a

import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_for_face_accounting_57972424

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) (hConn : L.Connected) (hV : 3 ≤ Fintype.card V) : L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_bound_for_face_accounting_57972424 L hDraw hConn hV
