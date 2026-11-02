-- Prove2me | solution 1 for WilliamsonShmoys.edgeFinset_card_mono__p2m_df5daf12_daf3_4429_a1d3_fb22e1c60853_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:53:51.750592+00:00
-- url     : https://prove2.me/submissions/8f701fdc-1d60-4b8c-ae35-76b0f7a74624

import Mathlib

theorem solution
    {V : Type} [Fintype V]
    (G F : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel F.Adj]
    (hGF : G ≤ F) :
    G.edgeFinset.card ≤ F.edgeFinset.card := by
  exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hGF)