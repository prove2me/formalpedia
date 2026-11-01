-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_euler_edge_bound__p2m_06e45311_b4a8_47cf_99af_36dad6983f39_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:40:38.763205+00:00
-- url     : https://prove2.me/submissions/282a1cbe-c6a7-4769-bbcc-fcdad9ae7186
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound__p2m_d0cbf8fc_b126_4e9b_9c59_f16faa272cb9_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_lower_bound__p2m_d0cbf8fc_b126_4e9b_9c59_f16faa272cb9_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ H' : SimpleGraph V,
      (∀ {u v : V}, H'.Adj u v → H.Adj u v) →
      HasPlanarDrawingOn H' → H' = H) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    H.edgeFinset.card = 3 * Fintype.card V - 6 := by
  letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
    fun G => Classical.decRel G.Adj
  have hupper := WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_d0cbf8fc_b126_4e9b_9c59_f16faa272cb9_a1 H hH hcard
  have hlower := WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_d0cbf8fc_b126_4e9b_9c59_f16faa272cb9_a1 H hH hcard hmax
  omega