-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_euler__p2m_2343a1b4_cbe5_4a48_b836_711e4285cb1c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:44:12.325583+00:00
-- url     : https://prove2.me/submissions/3010ee6c-479e-4d92-bf4c-68a7086c1a50

import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_count_from_drawing

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hconnected : H.Connected) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 :=
  WilliamsonShmoys.planar_drawing_euler_count_from_drawing H hplanar hconnected
