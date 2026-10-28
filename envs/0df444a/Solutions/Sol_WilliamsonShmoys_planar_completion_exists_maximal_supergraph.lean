-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_exists_maximal_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:31:33.902997+00:00
-- url     : https://prove2.me/submissions/f41d229b-3a6d-4966-89b8-1c28cd3cb60e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_graph_exists_edge_maximal

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      M.edgeSet ⊆ L.edgeSet ∧
      (∀ K : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn K →
        L.edgeSet ⊆ K.edgeSet → K.edgeSet = L.edgeSet) := by
  exact WilliamsonShmoys.finite_graph_exists_edge_maximal
    WilliamsonShmoys.HasPlanarDrawingOn M hM