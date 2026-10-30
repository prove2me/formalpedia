-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:04:23.974343+00:00
-- url     : https://prove2.me/submissions/720cafbe-4923-4d51-b569-365cf4687a95

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper__p2m_fe266be1_b394_4319_ae10_b52cb17a5e91_a1

open WilliamsonShmoys

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  first
  | exact _root_.WilliamsonShmoys.planar_drawing_edge_count_upper__p2m_fe266be1_b394_4319_ae10_b52cb17a5e91_a1
  | (apply _root_.WilliamsonShmoys.planar_drawing_edge_count_upper__p2m_fe266be1_b394_4319_ae10_b52cb17a5e91_a1 <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.planar_drawing_edge_count_upper__p2m_fe266be1_b394_4319_ae10_b52cb17a5e91_a1 <;> assumption)
