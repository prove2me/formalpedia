-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_3a18cd50_a833_4853_9055_3e93726fc3e4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:13:05.601174+00:00
-- url     : https://prove2.me/submissions/3cd8593a-3cfe-48c3-a412-77d27c5b1ed4

import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound__p2m_9e9ddd37_2fbe_4f2e_b4a6_63a4b0058d20_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_simple_graph_edge_lower_bound__p2m_9e9ddd37_2fbe_4f2e_b4a6_63a4b0058d20_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hMax : ∀ H : SimpleGraph V, M ≤ H → HasPlanarDrawingOn H → H = M)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.maximal_planar_simple_graph_edge_lower_bound__p2m_9e9ddd37_2fbe_4f2e_b4a6_63a4b0058d20_a1 M hM hMax hCard
  · exact WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_9e9ddd37_2fbe_4f2e_b4a6_63a4b0058d20_a1 M hM hCard