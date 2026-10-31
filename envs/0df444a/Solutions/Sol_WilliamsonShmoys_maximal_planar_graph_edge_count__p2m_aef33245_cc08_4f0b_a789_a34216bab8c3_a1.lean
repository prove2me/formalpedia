-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_aef33245_cc08_4f0b_a789_a34216bab8c3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:31:42.453307+00:00
-- url     : https://prove2.me/submissions/1f3a2deb-93f9-462e-84b3-e7e48ec85a94

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_5b1667b7_42bc_4fca_8b00_4cc76e33db8b_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_5b1667b7_42bc_4fca_8b00_4cc76e33db8b_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hMax : ∀ P : SimpleGraph V, N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    3 * Fintype.card V - 6 = N.edgeSet.ncard := by
  have hUpper := WilliamsonShmoys.planar_edge_upper_bound__p2m_5b1667b7_42bc_4fca_8b00_4cc76e33db8b_a1 N hCard hN
  have hLower := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_5b1667b7_42bc_4fca_8b00_4cc76e33db8b_a1 N hCard hN hMax
  omega