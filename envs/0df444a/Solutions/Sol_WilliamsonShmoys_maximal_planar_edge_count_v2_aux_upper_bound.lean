-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_v2_aux_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:04:56.87429+00:00
-- url     : https://prove2.me/submissions/fc5877b4-d907-460e-bb99-3f7efc87a3c7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_nontrivial_v2
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_euler_v2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hV : 3 <= Fintype.card V) :
    W.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨K, hWK, hKconn, hKdraw⟩ :=
    WilliamsonShmoys.planar_drawing_connected_supergraph_nontrivial_v2 W hdraw hV
  apply le_trans (Set.ncard_mono (SimpleGraph.edgeSet_mono hWK))
  exact WilliamsonShmoys.connected_planar_edge_bound_euler_v2 K hKconn hKdraw hV