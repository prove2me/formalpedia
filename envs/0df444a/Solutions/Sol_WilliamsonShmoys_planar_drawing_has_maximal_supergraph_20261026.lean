-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_supergraph_20261026
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:51:12.716581+00:00
-- url     : https://prove2.me/submissions/996dc50b-a6ac-42ee-8477-8138e2bbe7a3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_predicate_has_maximal_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
        ∀ P : SimpleGraph V, N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N := by
  exact WilliamsonShmoys.finite_predicate_has_maximal_extension
    (R := WilliamsonShmoys.HasPlanarDrawingOn) M hM