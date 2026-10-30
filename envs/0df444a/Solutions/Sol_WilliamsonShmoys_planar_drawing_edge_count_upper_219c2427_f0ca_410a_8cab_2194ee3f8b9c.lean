-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_upper_219c2427_f0ca_410a_8cab_2194ee3f8b9c
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:13:30.934291+00:00
-- url     : https://prove2.me/submissions/211f2a4c-bebe-48ba-944f-4605f3e3f1fa

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_20261028

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  first
  | exact _root_.WilliamsonShmoys.planar_drawing_edge_upper_bound_20261028
  | (apply _root_.WilliamsonShmoys.planar_drawing_edge_upper_bound_20261028 <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.planar_drawing_edge_upper_bound_20261028 <;> assumption)
