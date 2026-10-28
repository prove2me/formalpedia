-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_supergraph_for_euler_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T10:58:32.335603+00:00
-- url     : https://prove2.me/submissions/ea7b8959-13f2-48f0-8c65-4ed805c74259

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_above_in_finite_partial_order
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → L = M := by
  classical
  exact WilliamsonShmoys.exists_maximal_above_in_finite_partial_order
    K WilliamsonShmoys.HasPlanarDrawingOn hK