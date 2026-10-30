-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_upper_bound__p2m_f02ef8ad_5db5_4334_91a0_6b5d944fa80f_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:35:20.302977+00:00
-- url     : https://prove2.me/submissions/8b021795-a4cf-4b04-a639-588ac69e4bd2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_via_faces

set_option autoImplicit false

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
