-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_dabb2cbe_7fe3_4213_96ba_204afbbd922b
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:30:32.608325+00:00
-- url     : https://prove2.me/submissions/fb5455e7-682f-483f-b06c-2870abe03cd5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_lower_bound_dabb2cbe_7fe3_4213_96ba_204afbbd922b
import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_count_upper_bound_dabb2cbe_7fe3_4213_96ba_204afbbd922b
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hmax : ∀ Z : SimpleGraph V,
      Y ≤ Z → WilliamsonShmoys.HasPlanarDrawingOn Z → Z = Y) :
    3 * Fintype.card V = Y.edgeSet.ncard + 6 := by
  have hlo := WilliamsonShmoys.maximal_planar_graph_edge_count_lower_bound_dabb2cbe_7fe3_4213_96ba_204afbbd922b Y hV hY hmax
  have hhi := WilliamsonShmoys.planar_graph_edge_count_upper_bound_dabb2cbe_7fe3_4213_96ba_204afbbd922b Y hV hY
  omega