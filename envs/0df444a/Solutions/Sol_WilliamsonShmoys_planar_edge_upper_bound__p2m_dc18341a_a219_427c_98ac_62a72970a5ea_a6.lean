-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_dc18341a_a219_427c_98ac_62a72970a5ea_a6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:09:11.882852+00:00
-- url     : https://prove2.me/submissions/25c0fd09-973f-42ce-ba27-6b8075a123bb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_2026

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  first
  | exact _root_.WilliamsonShmoys.planar_simple_graph_edge_bound_2026
  | (apply _root_.WilliamsonShmoys.planar_simple_graph_edge_bound_2026 <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.planar_simple_graph_edge_bound_2026 <;> assumption)
