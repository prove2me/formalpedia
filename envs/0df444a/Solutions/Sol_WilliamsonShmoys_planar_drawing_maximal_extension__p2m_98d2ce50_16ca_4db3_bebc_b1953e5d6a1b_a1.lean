-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_98d2ce50_16ca_4db3_bebc_b1953e5d6a1b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:57:52.330143+00:00
-- url     : https://prove2.me/submissions/3a377989-b570-4963-ba82-9d70470f35a7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_finite_choice__p2m_168460db_bad2_471e_a83e_74dae3ce8af4_a2
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V,
      T ≤ U ∧ HasPlanarDrawingOn U ∧
        ∀ W : SimpleGraph V, U ≤ W → HasPlanarDrawingOn W → W = U := by
  exact WilliamsonShmoys.planar_drawing_maximal_extension_finite_choice__p2m_168460db_bad2_471e_a83e_74dae3ce8af4_a2
    T HasPlanarDrawingOn hT