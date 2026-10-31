-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_connected_extension_for_certificate_38ffb807
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:48:49.588998+00:00
-- url     : https://prove2.me/submissions/49262e11-acc2-4119-b878-d71b5cb805f4

import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_2c262075_af7a_40b5_8216_f56b847d81a6_a3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H :=
  WilliamsonShmoys.planar_drawing_connected_extension__p2m_2c262075_af7a_40b5_8216_f56b847d81a6_a3 K hV hdraw
