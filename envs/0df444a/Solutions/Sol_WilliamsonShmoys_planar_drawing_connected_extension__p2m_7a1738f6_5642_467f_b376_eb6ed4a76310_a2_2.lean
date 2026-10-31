-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_connected_extension__p2m_7a1738f6_5642_467f_b376_eb6ed4a76310_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:37:39.512992+00:00
-- url     : https://prove2.me/submissions/2e4720f3-914e-4c5a-a0d8-39b29d35fb88

import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_2c262075_af7a_40b5_8216_f56b847d81a6_a3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H :=
  WilliamsonShmoys.planar_drawing_connected_extension__p2m_2c262075_af7a_40b5_8216_f56b847d81a6_a3 K hV hK
