-- Prove2me | solution 1 for WilliamsonShmoys.planar_euler_face_count__p2m_c50fd7db_db60_4155_a74b_9f8219c920fe_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:01:44.188995+00:00
-- url     : https://prove2.me/submissions/76a37c83-747e-4da5-be78-f9c0be508051

import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_count_from_drawing

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hPlanar : HasPlanarDrawingOn H)
    (hConn : H.Connected) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 :=
  WilliamsonShmoys.planar_drawing_euler_count_from_drawing H hPlanar hConn
