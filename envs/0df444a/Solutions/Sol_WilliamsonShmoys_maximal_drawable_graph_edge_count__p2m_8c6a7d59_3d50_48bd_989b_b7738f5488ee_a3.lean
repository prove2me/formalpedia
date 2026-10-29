-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_8c6a7d59_3d50_48bd_989b_b7738f5488ee_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T21:36:45.819153+00:00
-- url     : https://prove2.me/submissions/45431001-137c-48b5-9682-3d0441108374
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_30825c49_c1ed_4d16_b870_dd4c24d4c0d7_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_lower_bound__p2m_30825c49_c1ed_4d16_b870_dd4c24d4c0d7_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V, M.edgeSet ⊆ N.edgeSet →
      HasPlanarDrawingOn N → N = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_edge_bound__p2m_30825c49_c1ed_4d16_b870_dd4c24d4c0d7_a1 M hM hCard
  have hLower := WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound__p2m_30825c49_c1ed_4d16_b870_dd4c24d4c0d7_a1 M hM hCard hmax
  omega