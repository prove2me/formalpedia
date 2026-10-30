-- Prove2me | solution 3 for WilliamsonShmoys.planar_drawing_euler_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:16:07.297399+00:00
-- url     : https://prove2.me/submissions/2e91a569-645e-4440-848b-d79852b4049f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_707fd91e

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  first
  | exact _root_.WilliamsonShmoys.planar_drawing_edge_upper_bound_707fd91e
  | (apply _root_.WilliamsonShmoys.planar_drawing_edge_upper_bound_707fd91e <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.planar_drawing_edge_upper_bound_707fd91e <;> assumption)
