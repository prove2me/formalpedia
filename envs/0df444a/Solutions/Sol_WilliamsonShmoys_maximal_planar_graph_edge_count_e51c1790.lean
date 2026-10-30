-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_e51c1790
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:50:52.465112+00:00
-- url     : https://prove2.me/submissions/c7d9ec26-1d87-4532-ac4a-8be14cef1fd7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_bound_e51c1790
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_lower_bound_e51c1790

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hmax : ∀ W : SimpleGraph V,
      U ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W → W = U) :
    3 * Fintype.card V = U.edgeSet.ncard + 6 := by
  have hu := WilliamsonShmoys.planar_graph_edge_bound_e51c1790 U hV hU
  have hl := WilliamsonShmoys.maximal_planar_graph_edge_lower_bound_e51c1790 U hV hU hmax
  exact Nat.le_antisymm hl hu