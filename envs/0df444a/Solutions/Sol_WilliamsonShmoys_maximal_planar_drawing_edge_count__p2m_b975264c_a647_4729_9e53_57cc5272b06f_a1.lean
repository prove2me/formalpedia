-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_b975264c_a647_4729_9e53_57cc5272b06f_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:35:54.250393+00:00
-- url     : https://prove2.me/submissions/a5911e20-6f67-4859-aba1-3646d5aacdc8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound__p2m_af9c4344_86bf_422f_95f1_74c23a123b22_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_af9c4344_86bf_422f_95f1_74c23a123b22_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) [DecidableRel L.Adj]
    (hL : HasPlanarDrawingOn L) (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    L.edgeFinset.card + 6 = 3 * Fintype.card V := by
  have hlow := WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_af9c4344_86bf_422f_95f1_74c23a123b22_a1
    L hL hcard hmax
  have hhigh := WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_af9c4344_86bf_422f_95f1_74c23a123b22_a1
    L hL hcard
  omega