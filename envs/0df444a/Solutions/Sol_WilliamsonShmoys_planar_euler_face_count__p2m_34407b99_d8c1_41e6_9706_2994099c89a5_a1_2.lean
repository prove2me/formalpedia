-- Prove2me | solution 2 for WilliamsonShmoys.planar_euler_face_count__p2m_34407b99_d8c1_41e6_9706_2994099c89a5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:52:20.234987+00:00
-- url     : https://prove2.me/submissions/a65503cc-a5e3-41d7-825a-cb74d532c38e

import Theorems.Thm_WilliamsonShmoys_connected_drawing_euler_face_count__p2m_74636254_a954_4b01_9b70_979bcb3da8e1_a3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 :=
  WilliamsonShmoys.connected_drawing_euler_face_count__p2m_74636254_a954_4b01_9b70_979bcb3da8e1_a3 G hG hconn
