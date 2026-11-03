-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_bound__p2m_1869d2b3_4acb_4df1_b926_664515403053_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:44:49.936301+00:00
-- url     : https://prove2.me/submissions/89c7e81f-98d5-4eb1-a212-90c506a38152

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_afc05135_ebe6_4750_8043_cdffdef73084_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax :
      ∀ K : SimpleGraph V,
        (∀ u v, H.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        ∀ u v, K.Adj u v → H.Adj u v) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card + 6 ≤ 3 * Fintype.card V) :=
  WilliamsonShmoys.planar_edge_count_upper_bound__p2m_afc05135_ebe6_4750_8043_cdffdef73084_a1 H hcard hdraw