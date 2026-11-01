-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_exact_edge_count__p2m_cb03d114_7f2d_468d_a111_d39943cc6a95_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:49:31.035266+00:00
-- url     : https://prove2.me/submissions/6c08d676-03f5-4f32-bd38-1da813da02f1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_bound__p2m_b3b14217_54f7_4da9_9b6d_f0fddbb566d2_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_lower_bound__p2m_b3b14217_54f7_4da9_9b6d_f0fddbb566d2_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V,
      (∀ u v, N.Adj u v → P.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn P →
      ∀ u v, P.Adj u v → N.Adj u v) :
    3 * Fintype.card V = N.edgeSet.ncard + 6 := by
  have h₁ := WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_b3b14217_54f7_4da9_9b6d_f0fddbb566d2_a1 N hV hN
  have h₂ := WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_b3b14217_54f7_4da9_9b6d_f0fddbb566d2_a1 N hV hN hmax
  omega