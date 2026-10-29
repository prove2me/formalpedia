-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension__p2m_2caa5445_5382_49b4_aef1_d1703ac143a6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:48:48.130387+00:00
-- url     : https://prove2.me/submissions/df4ee493-29b6-4d72-990c-636622356a9f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_extension__p2m_5c4a3429_2a1c_4098_a0a0_aed4ca251271_a2
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_mono__p2m_5c4a3429_2a1c_4098_a0a0_aed4ca251271_a2

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ H : SimpleGraph V,
      R ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  exact WilliamsonShmoys.finite_maximal_extension__p2m_5c4a3429_2a1c_4098_a0a0_aed4ca251271_a2
    (P := WilliamsonShmoys.HasPlanarDrawingOn)
    (hmono := WilliamsonShmoys.planarDrawingOn_mono__p2m_5c4a3429_2a1c_4098_a0a0_aed4ca251271_a2)
    (R := R) hR