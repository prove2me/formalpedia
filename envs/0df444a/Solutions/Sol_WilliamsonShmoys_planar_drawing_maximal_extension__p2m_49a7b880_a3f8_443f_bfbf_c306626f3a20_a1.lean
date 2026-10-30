-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_49a7b880_a3f8_443f_bfbf_c306626f3a20_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T06:50:18.718186+00:00
-- url     : https://prove2.me/submissions/2277310e-77d7-489b-936c-37467bcf6724

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_partial_order_maximal_extension__p2m_1ace3c40_0347_471f_a850_5688ff0e5a6a_a1
import Theorems.Thm_WilliamsonShmoys_finite_simple_graphs__p2m_1ace3c40_0347_471f_a850_5688ff0e5a6a_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L ≤ M →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M ≤ L := by
  letI : Finite (SimpleGraph V) :=
    WilliamsonShmoys.finite_simple_graphs__p2m_1ace3c40_0347_471f_a850_5688ff0e5a6a_a1
  exact WilliamsonShmoys.finite_partial_order_maximal_extension__p2m_1ace3c40_0347_471f_a850_5688ff0e5a6a_a1
    (P := WilliamsonShmoys.HasPlanarDrawingOn) K hK