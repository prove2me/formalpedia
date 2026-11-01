-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_extension_exists__p2m_6387f002_1fd9_417d_811a_77c2c095c6e5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:13:41.733194+00:00
-- url     : https://prove2.me/submissions/bf10a245-524e-4434-897d-945201255b96

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_by_edge_count__p2m_9642ee1f_f012_44b9_a1b9_1c78c6be4597_a1
import Theorems.Thm_WilliamsonShmoys_spanning_graph_eq_of_edge_card_le__p2m_9642ee1f_f012_44b9_a1b9_1c78c6be4597_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (letI : DecidableRel G.Adj := Classical.decRel G.Adj
       letI : DecidableRel H.Adj := Classical.decRel H.Adj
       G.edgeFinset.card ≤ H.edgeFinset.card) ∧
      (∀ K : SimpleGraph V,
        (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = H) := by
  classical
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_extension_by_edge_count__p2m_9642ee1f_f012_44b9_a1b9_1c78c6be4597_a1 G hG
  rcases hmax with ⟨hbase, hmax⟩
  refine ⟨H, hGH, hH, hbase, ?_⟩
  intro K hHK hK
  exact WilliamsonShmoys.spanning_graph_eq_of_edge_card_le__p2m_9642ee1f_f012_44b9_a1b9_1c78c6be4597_a1
    H K hHK (hmax K hHK hK)