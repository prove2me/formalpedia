-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_supergraph_with_edge_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:07:22.28598+00:00
-- url     : https://prove2.me/submissions/898a61bb-e35e-4ece-b386-bd3afa210ace
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_supergraph_with_edge_lower_bound_completion
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_supergraph_with_edge_lower_bound_maximal_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    ∃ Z : SimpleGraph V,
      Y ≤ Z ∧
      WilliamsonShmoys.HasPlanarDrawingOn Z ∧
      3 * Fintype.card V ≤ Z.edgeSet.ncard + 6 := by
  obtain ⟨Z, hYZ, hZ, hMax⟩ :=
    WilliamsonShmoys.planar_graph_has_supergraph_with_edge_lower_bound_completion Y hV hY
  exact ⟨Z, hYZ, hZ,
    WilliamsonShmoys.planar_graph_has_supergraph_with_edge_lower_bound_maximal_bound Z hV hZ hMax⟩