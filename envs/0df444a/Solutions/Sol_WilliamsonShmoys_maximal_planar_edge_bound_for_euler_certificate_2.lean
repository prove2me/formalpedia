-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_bound_for_euler_certificate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:14:04.297105+00:00
-- url     : https://prove2.me/submissions/0a071591-a56d-45d8-b367-47e6d80fc372

import Mathlib
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
