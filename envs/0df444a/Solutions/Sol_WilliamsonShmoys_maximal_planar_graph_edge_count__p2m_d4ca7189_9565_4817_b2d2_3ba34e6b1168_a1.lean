-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_d4ca7189_9565_4817_b2d2_3ba34e6b1168_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:20:54.317127+00:00
-- url     : https://prove2.me/submissions/b0b2ae5a-f630-4f13-928b-b4f79e495bb0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_upper_bound__p2m_b2b84f5d_edb7_4ceb_baef_13a00af24ad7_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_lower_bound__p2m_b2b84f5d_edb7_4ceb_baef_13a00af24ad7_a1
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V) (hDraw : HasPlanarDrawingOn R) (hV : 3 ≤ Fintype.card V) (hmax : ∀ S : SimpleGraph V, R.edgeSet ⊆ S.edgeSet → HasPlanarDrawingOn S → S.edgeSet ⊆ R.edgeSet) : R.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.maximal_planar_graph_edge_upper_bound__p2m_b2b84f5d_edb7_4ceb_baef_13a00af24ad7_a1 R hDraw hV
  have hLower := WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_b2b84f5d_edb7_4ceb_baef_13a00af24ad7_a1 R hDraw hV hmax
  exact Nat.le_antisymm hUpper hLower