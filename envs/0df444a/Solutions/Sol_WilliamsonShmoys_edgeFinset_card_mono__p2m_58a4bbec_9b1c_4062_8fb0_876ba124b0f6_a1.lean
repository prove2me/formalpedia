-- Prove2me | solution 1 for WilliamsonShmoys.edgeFinset_card_mono__p2m_58a4bbec_9b1c_4062_8fb0_876ba124b0f6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:14:53.537415+00:00
-- url     : https://prove2.me/submissions/d5226786-ac17-4ebe-a3ec-45a57db40321

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel K.Adj]
    (hsub : ∀ u v : V, G.Adj u v → K.Adj u v) :
    G.edgeFinset.card ≤ K.edgeFinset.card := by
  have hle : G ≤ K := fun u v huv => hsub u v huv
  exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hle)