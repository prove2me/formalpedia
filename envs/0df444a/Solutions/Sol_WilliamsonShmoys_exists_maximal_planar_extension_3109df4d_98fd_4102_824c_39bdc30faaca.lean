-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_extension_3109df4d_98fd_4102_824c_39bdc30faaca
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:26:16.867882+00:00
-- url     : https://prove2.me/submissions/0e6f1d71-afc6-43d4-80f7-6f25b084bb47

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_predicate_extension

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, HasPlanarDrawingOn K ∧
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      (∀ L : SimpleGraph V, HasPlanarDrawingOn L →
        (∀ u v, K.Adj u v → L.Adj u v) →
        ∀ u v, L.Adj u v → K.Adj u v) := by
  exact WilliamsonShmoys.finite_maximal_predicate_extension
    (P := HasPlanarDrawingOn) H hH