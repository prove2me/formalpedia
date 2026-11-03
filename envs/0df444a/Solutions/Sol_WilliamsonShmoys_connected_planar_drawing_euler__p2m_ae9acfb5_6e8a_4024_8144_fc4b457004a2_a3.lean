-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_euler__p2m_ae9acfb5_6e8a_4024_8144_fc4b457004a2_a3
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:51:13.358029+00:00
-- url     : https://prove2.me/submissions/60ab66d9-de0d-4daa-b5d4-7cae11650f38

import Theorems.Thm_WilliamsonShmoys_connected_planar_euler_formula__p2m_034f5ef2_6768_4eb9_83c3_8c1c8d5ce02b_a2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeFinset.card + 2 :=
  WilliamsonShmoys.connected_planar_euler_formula__p2m_034f5ef2_6768_4eb9_83c3_8c1c8d5ce02b_a2 H hH hconn