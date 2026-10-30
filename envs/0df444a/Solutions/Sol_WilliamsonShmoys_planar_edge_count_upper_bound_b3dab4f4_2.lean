-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_count_upper_bound_b3dab4f4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:44:39.610495+00:00
-- url     : https://prove2.me/submissions/ce2671ba-242f-48c6-9bb3-49d33a4cad77

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_for_maximal_count_957bde25

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    L.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  first
  | exact _root_.WilliamsonShmoys.planar_drawing_edge_bound_for_maximal_count_957bde25
  | (apply _root_.WilliamsonShmoys.planar_drawing_edge_bound_for_maximal_count_957bde25 <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.planar_drawing_edge_bound_for_maximal_count_957bde25 <;> assumption)
