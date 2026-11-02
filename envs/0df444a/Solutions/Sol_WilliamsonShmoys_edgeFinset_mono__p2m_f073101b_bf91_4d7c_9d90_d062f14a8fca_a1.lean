-- Prove2me | solution 1 for WilliamsonShmoys.edgeFinset_mono__p2m_f073101b_bf91_4d7c_9d90_d062f14a8fca_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:52:13.453876+00:00
-- url     : https://prove2.me/submissions/bf320340-e5c2-4ca0-ba28-036e5bf17a01

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (hGH : G ≤ H) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     letI : DecidableRel H.Adj := Classical.decRel H.Adj
     G.edgeFinset.card ≤ H.edgeFinset.card) := by
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hGH)