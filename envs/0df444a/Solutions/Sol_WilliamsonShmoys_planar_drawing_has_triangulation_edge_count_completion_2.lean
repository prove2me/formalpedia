-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_has_triangulation_edge_count_completion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:11:44.17273+00:00
-- url     : https://prove2.me/submissions/860860a8-016d-426b-88fc-db24283953b0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count__p2m_295c0ef8_5d8f_41a3_8c9f_ccd6cdcf9c48_a2

set_option autoImplicit false

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  first
  | exact _root_.WilliamsonShmoys.planar_completion_edge_count__p2m_295c0ef8_5d8f_41a3_8c9f_ccd6cdcf9c48_a2
  | (apply _root_.WilliamsonShmoys.planar_completion_edge_count__p2m_295c0ef8_5d8f_41a3_8c9f_ccd6cdcf9c48_a2 <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.planar_completion_edge_count__p2m_295c0ef8_5d8f_41a3_8c9f_ccd6cdcf9c48_a2 <;> assumption)
