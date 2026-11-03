-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_1634faf2_3284_496c_bfc9_f8ff236eda71_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:46:52.964576+00:00
-- url     : https://prove2.me/submissions/28664b88-798b-406b-b7de-b0b67a21f537

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_4f438a2b_7c24_414a_8cb6_3aa4d799f4d5_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_4f438a2b_7c24_414a_8cb6_3aa4d799f4d5_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, G ≤ M → HasPlanarDrawingOn M → M = G) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     letI : Fintype ↑G.edgeSet := Fintype.ofFinite _
     3 * Fintype.card V = G.edgeFinset.card + 6) := by
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  letI : Fintype ↑G.edgeSet := Fintype.ofFinite _
  have hupper := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_4f438a2b_7c24_414a_8cb6_3aa4d799f4d5_a1 G hG hV
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_4f438a2b_7c24_414a_8cb6_3aa4d799f4d5_a1 G hG hV hmax
  exact Nat.le_antisymm hlower hupper