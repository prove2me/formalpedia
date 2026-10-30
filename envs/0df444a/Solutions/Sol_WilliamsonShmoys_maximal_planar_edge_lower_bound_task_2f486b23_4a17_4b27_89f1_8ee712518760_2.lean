-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_lower_bound_task_2f486b23_4a17_4b27_89f1_8ee712518760
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:14:40.801916+00:00
-- url     : https://prove2.me/submissions/82db7a46-cfe9-407d-bc9b-4416b6f23a62

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound_707fd91e

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by
  first
  | exact _root_.WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_707fd91e
  | (apply _root_.WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_707fd91e <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_707fd91e <;> assumption)
