-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_extension__p2m_28646a36_1b88_4c0c_9520_4ba110528cb4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:34:54.317618+00:00
-- url     : https://prove2.me/submissions/60b17429-5d09-403b-814c-22aedb04a52c

import Theorems.Thm_WilliamsonShmoys_triangulation_completion_finite_maximal_drawable_37d910a7_7508_48a8_9dea_1ce0a7ac4e79

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    exists M : SimpleGraph V, L <= M /\
      WilliamsonShmoys.HasPlanarDrawingOn M /\
      (forall N : SimpleGraph V, M <= N ->
        WilliamsonShmoys.HasPlanarDrawingOn N -> N = M) :=
  WilliamsonShmoys.triangulation_completion_finite_maximal_drawable_37d910a7_7508_48a8_9dea_1ce0a7ac4e79 L hDraw
