-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_maximal_extension_for_triangulated_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T16:48:44.175184+00:00
-- url     : https://prove2.me/submissions/42255e12-5c5e-41f0-940a-ae7a69de105d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_extension_on_finite_simple_graphs

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by
  exact WilliamsonShmoys.finite_maximal_extension_on_finite_simple_graphs
    WilliamsonShmoys.HasPlanarDrawingOn H hDraw