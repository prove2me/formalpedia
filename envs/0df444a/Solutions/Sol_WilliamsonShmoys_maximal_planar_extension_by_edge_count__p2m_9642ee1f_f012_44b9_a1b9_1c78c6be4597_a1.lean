-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension_by_edge_count__p2m_9642ee1f_f012_44b9_a1b9_1c78c6be4597_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:17:15.344944+00:00
-- url     : https://prove2.me/submissions/61d9371a-efcc-42a4-9199-53b06007348b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_simpleGraph_extension_by_edge_count__p2m_f330d4c2_9c1a_4a03_91e8_570c68857cc4_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (letI : DecidableRel G.Adj := Classical.decRel G.Adj
       letI : DecidableRel H.Adj := Classical.decRel H.Adj
       G.edgeFinset.card ≤ H.edgeFinset.card) ∧
      ∀ K : SimpleGraph V,
        (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K →
          (letI : DecidableRel H.Adj := Classical.decRel H.Adj
           letI : DecidableRel K.Adj := Classical.decRel K.Adj
           K.edgeFinset.card ≤ H.edgeFinset.card) := by
  exact WilliamsonShmoys.exists_maximal_simpleGraph_extension_by_edge_count__p2m_f330d4c2_9c1a_4a03_91e8_570c68857cc4_a1
    WilliamsonShmoys.HasPlanarDrawingOn G hG