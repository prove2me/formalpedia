-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_count_of_drawing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:17:24.43036+00:00
-- url     : https://prove2.me/submissions/6e5d2738-db0c-4cce-8665-5d059d579118

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_707fd91e

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  first
  | exact _root_.WilliamsonShmoys.planar_drawing_edge_upper_bound_707fd91e
  | (apply _root_.WilliamsonShmoys.planar_drawing_edge_upper_bound_707fd91e <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.planar_drawing_edge_upper_bound_707fd91e <;> assumption)
