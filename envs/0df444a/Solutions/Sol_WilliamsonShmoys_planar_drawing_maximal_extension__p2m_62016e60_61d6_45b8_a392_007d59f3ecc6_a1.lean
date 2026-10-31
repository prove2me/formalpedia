-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_62016e60_61d6_45b8_a392_007d59f3ecc6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:34:10.609584+00:00
-- url     : https://prove2.me/submissions/ef4d9f32-38ef-4ae2-9aa2-5d811781cc3b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_supergraph__p2m_3043441f_698f_49eb_9867_9197561360be_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V, K ≤ L →
          WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by
  exact WilliamsonShmoys.finite_maximal_supergraph__p2m_3043441f_698f_49eb_9867_9197561360be_a1
    (V := V) H WilliamsonShmoys.HasPlanarDrawingOn hH