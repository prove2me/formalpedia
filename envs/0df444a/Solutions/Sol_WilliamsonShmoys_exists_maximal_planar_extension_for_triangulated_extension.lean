-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_extension_for_triangulated_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:23:10.040718+00:00
-- url     : https://prove2.me/submissions/e85cc130-0550-4bfa-a301-0cf62fab2c0d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_for_finite_predicate

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by
  exact WilliamsonShmoys.exists_maximal_extension_for_finite_predicate
    (P := WilliamsonShmoys.HasPlanarDrawingOn) K hDrawing