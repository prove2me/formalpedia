-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_extension_maximal_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:49:06.552431+00:00
-- url     : https://prove2.me/submissions/e65fa385-13a0-4b9d-bbb3-e3039228ca69

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_count_upper_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_lower_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper := WilliamsonShmoys.planar_graph_edge_count_upper_bound L hL hV
  have hLower := WilliamsonShmoys.maximal_planar_graph_edge_count_lower_bound L hL hMax hV
  omega