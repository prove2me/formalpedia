-- Prove2me | solution 2 for WilliamsonShmoys.connected_planar_drawing_euler_face_count__p2m_5d599c83_54c6_426b_a50f_1d6092e7f607_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:41:18.655045+00:00
-- url     : https://prove2.me/submissions/f8c0e49d-692c-4af5-97b4-2d7dc4474b05

import Theorems.Thm_WilliamsonShmoys_drawingOn_face_count_bounds

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hConn : H.Connected) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : ∃ f : Nat, Fintype.card V + f = H.edgeSet.ncard + 2 ∧ 3 * f ≤ 2 * H.edgeSet.ncard :=
  WilliamsonShmoys.drawingOn_face_count_bounds H hConn hDraw hV
