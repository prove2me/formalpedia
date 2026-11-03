-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_4f438a2b_7c24_414a_8cb6_3aa4d799f4d5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T05:16:05.151373+00:00
-- url     : https://prove2.me/submissions/1648d7b5-0397-485e-9fb8-65da55c06506

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_7b71df04_d9fa_431d_9970_a3959e705ba4_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, G ≤ M → HasPlanarDrawingOn M → M = G) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     letI : Fintype ↑G.edgeSet := Fintype.ofFinite _
     3 * Fintype.card V ≤ G.edgeFinset.card + 6) := by
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  letI : Fintype ↑G.edgeSet := Fintype.ofFinite _
  change 3 * Fintype.card V ≤ G.edgeFinset.card + 6
  have hedge : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  rw [← hedge]
  exact WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_7b71df04_d9fa_431d_9970_a3959e705ba4_a1 G hV hG hmax
