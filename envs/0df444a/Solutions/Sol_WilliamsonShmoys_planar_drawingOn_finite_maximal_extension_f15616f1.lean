-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_finite_maximal_extension_f15616f1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T16:51:44.785621+00:00
-- url     : https://prove2.me/submissions/37706d41-312f-4c11-bc8e-90c30c129632

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_partialOrder_maximal_extension
import Theorems.Thm_WilliamsonShmoys_finite_simpleGraph_of_fintype

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ J : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn J →
        H ≤ J → H = J := by
  letI : Finite (SimpleGraph V) :=
    WilliamsonShmoys.finite_simpleGraph_of_fintype
  exact WilliamsonShmoys.finite_partialOrder_maximal_extension
    WilliamsonShmoys.HasPlanarDrawingOn K hK