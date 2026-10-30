-- Prove2me | solution 1 for WilliamsonShmoys.simpleGraph_edgeFinset_card_mono__p2m_4994fa52_8694_420c_b1ad_06ee126d888c_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:32:29.548355+00:00
-- url     : https://prove2.me/submissions/f6011a2c-bd64-407e-b9e1-81ce0a6f435b

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hGH : G ≤ H) :
    G.edgeFinset.card ≤ H.edgeFinset.card := by
  exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hGH)