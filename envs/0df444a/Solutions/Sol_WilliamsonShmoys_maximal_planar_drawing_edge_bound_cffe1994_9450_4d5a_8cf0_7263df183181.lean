-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_bound_cffe1994_9450_4d5a_8cf0_7263df183181
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:46:46.274641+00:00
-- url     : https://prove2.me/submissions/f826969b-c856-4447-9964-e3ef62acd9b3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound_repair_cffe1994_9450_4d5a_8cf0_7263df183181

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : forall N : SimpleGraph V,
      M <= N ->
      WilliamsonShmoys.HasPlanarDrawingOn N ->
      N = M) :
    3 * Fintype.card V - 6 <= M.edgeSet.ncard := by
  first
  | exact _root_.WilliamsonShmoys.maximal_planar_drawing_edge_bound_repair_cffe1994_9450_4d5a_8cf0_7263df183181
  | (apply _root_.WilliamsonShmoys.maximal_planar_drawing_edge_bound_repair_cffe1994_9450_4d5a_8cf0_7263df183181 <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.maximal_planar_drawing_edge_bound_repair_cffe1994_9450_4d5a_8cf0_7263df183181 <;> assumption)
