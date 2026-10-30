-- Prove2me | solution 3 for WilliamsonShmoys.maximal_planar_drawing_edge_count_c00979a8_planar_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:18:00.520178+00:00
-- url     : https://prove2.me/submissions/b2798900-6a1c-438b-b1e9-1498ba10fcd1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_707fd91e

set_option autoImplicit false
theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 <= Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  first
  | exact _root_.WilliamsonShmoys.planar_drawing_edge_upper_bound_707fd91e
  | (apply _root_.WilliamsonShmoys.planar_drawing_edge_upper_bound_707fd91e <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.planar_drawing_edge_upper_bound_707fd91e <;> assumption)
