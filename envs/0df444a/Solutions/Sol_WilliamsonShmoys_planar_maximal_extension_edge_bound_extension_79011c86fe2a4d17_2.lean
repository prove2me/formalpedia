-- Prove2me | solution 2 for WilliamsonShmoys.planar_maximal_extension_edge_bound_extension_79011c86fe2a4d17
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:39:12.931683+00:00
-- url     : https://prove2.me/submissions/bfbb3ffe-bef7-4912-b4b5-f4e596c95f21

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_extension_edge_bound_extension_79011c86fe2a4d17

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    Exists fun N : SimpleGraph V => M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ P : SimpleGraph V, N ≤ P →
        WilliamsonShmoys.HasPlanarDrawingOn P → P ≤ N := by
  exact WilliamsonShmoys.finite_maximal_extension_edge_bound_extension_79011c86fe2a4d17
    M WilliamsonShmoys.HasPlanarDrawingOn hM