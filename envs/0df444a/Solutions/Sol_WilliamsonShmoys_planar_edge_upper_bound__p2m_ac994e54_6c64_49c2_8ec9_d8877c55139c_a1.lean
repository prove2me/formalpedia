-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_ac994e54_6c64_49c2_8ec9_d8877c55139c_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:09:06.270483+00:00
-- url     : https://prove2.me/submissions/ca90abb4-5be2-411b-b321-e6f21a4f1af6

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_707fd91e

set_option autoImplicit false

open WilliamsonShmoys
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
