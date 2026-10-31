-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_extension_exists__p2m_2facc1d9_8574_46e5_b6ec_a0ba2784b822_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:44:19.587662+00:00
-- url     : https://prove2.me/submissions/002ee263-6240-4c48-9e6f-8fe6ba116d14

import Theorems.Thm_WilliamsonShmoys_planar_drawing_finite_maximal_extension_ws

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V,
      G ≤ L ∧
        WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ H : SimpleGraph V, L ≤ H →
          WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ L :=
  WilliamsonShmoys.planar_drawing_finite_maximal_extension_ws G hG
