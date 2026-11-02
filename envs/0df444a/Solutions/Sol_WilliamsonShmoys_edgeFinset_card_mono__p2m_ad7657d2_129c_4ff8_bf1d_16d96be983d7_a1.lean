-- Prove2me | solution 1 for WilliamsonShmoys.edgeFinset_card_mono__p2m_ad7657d2_129c_4ff8_bf1d_16d96be983d7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:57:54.176726+00:00
-- url     : https://prove2.me/submissions/fb854e98-15e3-4f04-84c4-0cbc0bd977ee

import Mathlib

theorem solution
    {V : Type} [Fintype V]
    (H G : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel G.Adj]
    (hHG : H ≤ G) :
    H.edgeFinset.card ≤ G.edgeFinset.card := by
  exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hHG)