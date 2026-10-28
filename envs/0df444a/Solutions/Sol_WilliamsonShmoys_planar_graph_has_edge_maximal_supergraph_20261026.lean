-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_edge_maximal_supergraph_20261026
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:23:15.312666+00:00
-- url     : https://prove2.me/submissions/79eaa746-cfd2-4819-ba58-6af68cce0792

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_FiniteGraph_exists_maximal_extension

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ J : SimpleGraph V,
        K ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = K := by
  exact FiniteGraph.exists_maximal_extension WilliamsonShmoys.HasPlanarDrawingOn H hH