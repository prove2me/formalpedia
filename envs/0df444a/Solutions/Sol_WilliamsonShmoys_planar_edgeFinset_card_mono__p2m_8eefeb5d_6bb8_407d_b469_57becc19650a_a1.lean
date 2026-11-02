-- Prove2me | solution 1 for WilliamsonShmoys.planar_edgeFinset_card_mono__p2m_8eefeb5d_6bb8_407d_b469_57becc19650a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:38:19.481201+00:00
-- url     : https://prove2.me/submissions/f05c6f3a-0028-453e-8892-9c403b359bd7

import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hGH : ∀ u v, G.Adj u v → H.Adj u v) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     letI : DecidableRel H.Adj := Classical.decRel H.Adj
     G.edgeFinset.card ≤ H.edgeFinset.card) := by
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hGH)