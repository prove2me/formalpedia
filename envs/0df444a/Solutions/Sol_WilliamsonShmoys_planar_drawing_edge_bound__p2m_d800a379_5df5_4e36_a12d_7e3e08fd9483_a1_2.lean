-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_d800a379_5df5_4e36_a12d_7e3e08fd9483_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:33:41.917311+00:00
-- url     : https://prove2.me/submissions/c28d348f-790f-4811-83b2-bb020b6138c5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_via_faces

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  first
  | exact _root_.WilliamsonShmoys.planar_edge_count_upper_bound_via_faces
  | (apply _root_.WilliamsonShmoys.planar_edge_count_upper_bound_via_faces <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.planar_edge_count_upper_bound_via_faces <;> assumption)
