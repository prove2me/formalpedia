-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_upper_bound__p2m_513f0e25_8b21_45bc_8db8_f06f4ba42a04_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:07:14.380883+00:00
-- url     : https://prove2.me/submissions/e01dbf0f-d495-4fc3-a556-d5a1674a1141

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_upper_bound__p2m_117a5bc6_0e8c_496f_accb_a7c904e7cb02_a1

open WilliamsonShmoys

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  first
  | exact _root_.WilliamsonShmoys.maximal_drawable_graph_edge_count_upper_bound__p2m_117a5bc6_0e8c_496f_accb_a7c904e7cb02_a1
  | (apply _root_.WilliamsonShmoys.maximal_drawable_graph_edge_count_upper_bound__p2m_117a5bc6_0e8c_496f_accb_a7c904e7cb02_a1 <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.maximal_drawable_graph_edge_count_upper_bound__p2m_117a5bc6_0e8c_496f_accb_a7c904e7cb02_a1 <;> assumption)
