-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_count_upper_c4011bda_e2a2_4391_a47d_b4ea4febecd9
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:10:31.161261+00:00
-- url     : https://prove2.me/submissions/2e22f6ea-3825-4edf-a578-0cc042ceff47

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_2026
set_option autoImplicit false
open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  first
  | exact _root_.WilliamsonShmoys.planar_simple_graph_edge_bound_2026
  | (apply _root_.WilliamsonShmoys.planar_simple_graph_edge_bound_2026 <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.planar_simple_graph_edge_bound_2026 <;> assumption)
