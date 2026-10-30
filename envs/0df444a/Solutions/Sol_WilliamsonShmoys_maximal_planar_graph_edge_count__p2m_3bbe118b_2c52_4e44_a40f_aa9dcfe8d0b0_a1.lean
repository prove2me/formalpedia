-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_3bbe118b_2c52_4e44_a40f_aa9dcfe8d0b0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:49:45.141993+00:00
-- url     : https://prove2.me/submissions/f76151fe-7bac-4382-a084-52a37b85dcba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_82506e18_7d6a_422e_80a5_205ab3f947ca_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_82506e18_7d6a_422e_80a5_205ab3f947ca_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hDraw : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_drawing_edge_bound__p2m_82506e18_7d6a_422e_80a5_205ab3f947ca_a1 M hDraw hCard
  have hLower := WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_82506e18_7d6a_422e_80a5_205ab3f947ca_a1 M hDraw hCard hMax
  omega