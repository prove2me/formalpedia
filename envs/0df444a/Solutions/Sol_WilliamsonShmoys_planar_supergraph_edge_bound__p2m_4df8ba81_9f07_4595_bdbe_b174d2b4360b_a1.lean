-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_bound__p2m_4df8ba81_9f07_4595_bdbe_b174d2b4360b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:57:37.453789+00:00
-- url     : https://prove2.me/submissions/2a5669f5-5cd8-4a63-b95c-a79718b524d4

import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_bound__p2m_4df8ba81_9f07_4595_bdbe_b174d2b4360b_a3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    ∃ K : SimpleGraph V, H <= K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       3 * Fintype.card V <= K.edgeFinset.card + 6) :=
  WilliamsonShmoys.planar_supergraph_edge_bound__p2m_4df8ba81_9f07_4595_bdbe_b174d2b4360b_a3 H hH hcard