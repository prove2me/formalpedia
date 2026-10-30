-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_edge_bound_bf226c5d
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:39:26.582116+00:00
-- url     : https://prove2.me/submissions/0435cfc6-869b-45f1-bd0c-db97c5a54ede

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound_connected_bf226c5d
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound_drawing_induce_bf226c5d
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound_components_bf226c5d

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  apply WilliamsonShmoys.planar_simple_edge_bound_components_bf226c5d G hV
  intro S instS hS hConnected
  exact WilliamsonShmoys.planar_simple_edge_bound_connected_bf226c5d
    (G.induce S) hS hConnected
    (WilliamsonShmoys.planar_simple_edge_bound_drawing_induce_bf226c5d G hG S)