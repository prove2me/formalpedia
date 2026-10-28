-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:08:59.19908+00:00
-- url     : https://prove2.me/submissions/92b98d4e-aeaa-41b2-a3e9-6d9cb249512a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ T : SimpleGraph V,
      G ≤ T ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      ∀ H : SimpleGraph V,
        T ≤ H →
        WilliamsonShmoys.HasPlanarDrawingOn H →
        H ≤ T := by
  exact WilliamsonShmoys.finite_maximal_extension
    (P := WilliamsonShmoys.HasPlanarDrawingOn) G hG