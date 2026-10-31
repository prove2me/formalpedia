-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_has_exact_edge_count__p2m_27144f45_411a_4982_b72d_bbbc3f64b45b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:45:28.477989+00:00
-- url     : https://prove2.me/submissions/c0ed2624-435b-4e76-823b-115b36c05e26

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_count_upper_bound__p2m_7ed45ce9_fab7_4799_9a3a_4afc5611b50c_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_lower_bound__p2m_7ed45ce9_fab7_4799_9a3a_4afc5611b50c_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ P : SimpleGraph V, N ≤ P → HasPlanarDrawingOn P → P = N) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.planar_graph_edge_count_upper_bound__p2m_7ed45ce9_fab7_4799_9a3a_4afc5611b50c_a2 N hDraw hV
  · exact WilliamsonShmoys.maximal_planar_graph_edge_count_lower_bound__p2m_7ed45ce9_fab7_4799_9a3a_4afc5611b50c_a2 N hDraw hV hMax