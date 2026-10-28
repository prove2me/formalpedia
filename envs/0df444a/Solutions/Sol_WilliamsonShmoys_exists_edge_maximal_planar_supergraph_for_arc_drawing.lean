-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_supergraph_for_arc_drawing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:28:38.584365+00:00
-- url     : https://prove2.me/submissions/480b2aaf-e231-4fe7-a4d1-e0a514b3621f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_finite_vertex_type

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M := by
  exact WilliamsonShmoys.exists_maximal_supergraph_for_finite_vertex_type
    (P := WilliamsonShmoys.HasPlanarDrawingOn) L hL