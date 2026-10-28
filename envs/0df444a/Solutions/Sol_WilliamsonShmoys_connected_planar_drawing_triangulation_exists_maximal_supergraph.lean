-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_triangulation_exists_maximal_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:20:02.847742+00:00
-- url     : https://prove2.me/submissions/fcb5a692-8c4a-4126-9e6d-ae8e858efa62

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_supergraph_maximality

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v⦄, G.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        (∀ ⦃u v⦄, H.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  exact finite_supergraph_maximality G WilliamsonShmoys.HasPlanarDrawingOn hG