-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_monotone__p2m_56609264_6a9a_4229_a716_b7a8ddd670b3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:35:39.40171+00:00
-- url     : https://prove2.me/submissions/964d0d3e-ceb7-4c28-8d67-8acddc3a7b15

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V]
    (L H : SimpleGraph V) (hLH : L ≤ H) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    L.edgeFinset.card ≤ H.edgeFinset.card := by
  classical
  exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hLH)