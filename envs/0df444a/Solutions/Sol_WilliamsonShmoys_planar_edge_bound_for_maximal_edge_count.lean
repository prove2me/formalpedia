-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_for_maximal_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:53:19.691968+00:00
-- url     : https://prove2.me/submissions/24ab9cb0-7af2-497b-bc0b-20d86f84ce1d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_20261028

set_option autoImplicit false

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  first
  | exact _root_.WilliamsonShmoys.planar_drawing_edge_upper_bound_20261028
  | (apply _root_.WilliamsonShmoys.planar_drawing_edge_upper_bound_20261028 <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.planar_drawing_edge_upper_bound_20261028 <;> assumption)
