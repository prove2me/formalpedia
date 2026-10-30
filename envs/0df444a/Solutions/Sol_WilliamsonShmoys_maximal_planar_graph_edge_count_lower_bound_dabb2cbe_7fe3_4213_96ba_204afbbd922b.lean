-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_lower_bound_dabb2cbe_7fe3_4213_96ba_204afbbd922b
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:44:56.227156+00:00
-- url     : https://prove2.me/submissions/f18ff0e1-4b1f-4241-8e43-8c782eba5df6

import Theorems.Thm_WilliamsonShmoys_planar_graph_has_supergraph_with_edge_lower_bound
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hmax : ∀ Z : SimpleGraph V,
      Y ≤ Z → WilliamsonShmoys.HasPlanarDrawingOn Z → Z = Y) :
    3 * Fintype.card V ≤ Y.edgeSet.ncard + 6 := by
  obtain ⟨Z, hYZ, hZ, hbound⟩ :=
    WilliamsonShmoys.planar_graph_has_supergraph_with_edge_lower_bound Y hV hY
  have hEq : Z = Y := hmax Z hYZ hZ
  rw [← hEq]
  exact hbound