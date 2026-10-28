-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_on_for_arcs
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:22:01.830708+00:00
-- url     : https://prove2.me/submissions/82cd6279-75d0-4074-bddb-1657f93c2f62

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_property

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V,
        N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N := by
  exact WilliamsonShmoys.exists_maximal_supergraph_of_property
    M WilliamsonShmoys.HasPlanarDrawingOn hDrawing