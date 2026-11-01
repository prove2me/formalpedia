-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_edge_count__p2m_e52a5279_3bb4_4190_b470_b345cecfed03_a4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:14:33.996237+00:00
-- url     : https://prove2.me/submissions/b1cd6af7-fa4a-4723-a53f-f9d75e96e51a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_9b84e475_7be1_4007_a2e0_d2e99948fc5d_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hH : HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, HasPlanarDrawingOn K →
        (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
        (∀ ⦃u v : V⦄, K.Adj u v → H.Adj u v))
    (hsub : ∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v)
    (dG : DecidableRel G.Adj)
    (dH : DecidableRel H.Adj)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := dG;
      G.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  exact WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_9b84e475_7be1_4007_a2e0_d2e99948fc5d_a2
    G hG dG hcard