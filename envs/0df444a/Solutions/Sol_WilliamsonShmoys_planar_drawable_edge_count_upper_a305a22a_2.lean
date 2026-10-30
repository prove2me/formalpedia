-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawable_edge_count_upper_a305a22a
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:18:32.680788+00:00
-- url     : https://prove2.me/submissions/5ca9e0c0-8096-41ba-80ef-28416f6e6b07

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_707fd91e

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  first
  | exact _root_.WilliamsonShmoys.planar_drawing_edge_upper_bound_707fd91e
  | (apply _root_.WilliamsonShmoys.planar_drawing_edge_upper_bound_707fd91e <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.planar_drawing_edge_upper_bound_707fd91e <;> assumption)
