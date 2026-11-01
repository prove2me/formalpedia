-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_count__p2m_abda76d0_f206_4b5c_973f_e20fb605b671_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:23:07.352024+00:00
-- url     : https://prove2.me/submissions/188050a9-0699-42e7-93fb-7cdc68fb01e3

import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_count_from_drawing

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hcard : 3 <= Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 :=
  WilliamsonShmoys.planar_drawing_euler_count_from_drawing G hplanar hconn
