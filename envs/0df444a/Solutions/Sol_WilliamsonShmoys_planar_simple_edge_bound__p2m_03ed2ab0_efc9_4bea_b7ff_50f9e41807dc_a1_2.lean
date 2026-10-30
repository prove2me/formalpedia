-- Prove2me | solution 2 for WilliamsonShmoys.planar_simple_edge_bound__p2m_03ed2ab0_efc9_4bea_b7ff_50f9e41807dc_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:09:18.183981+00:00
-- url     : https://prove2.me/submissions/7a16ce70-94a6-4584-802f-839a6fca4521

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
