-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_for_triangulation_extension_v2_0463fea4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:07:47.661119+00:00
-- url     : https://prove2.me/submissions/2573b789-3f81-4e2c-93ca-49dd53867e31

import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_for_triangulation_extension_v2_0463fea4
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_for_triangulation_extension_v2_0463fea4

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hCard : 3 <= Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hmax : forall S : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn S ->
      Set.Subset R.edgeSet S.edgeSet ->
      S.edgeSet = R.edgeSet) :
    R.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.planar_edge_count_upper_bound_for_triangulation_extension_v2_0463fea4 R hCard hR
  · exact WilliamsonShmoys.maximal_planar_edge_count_lower_bound_for_triangulation_extension_v2_0463fea4 R hCard hR hmax