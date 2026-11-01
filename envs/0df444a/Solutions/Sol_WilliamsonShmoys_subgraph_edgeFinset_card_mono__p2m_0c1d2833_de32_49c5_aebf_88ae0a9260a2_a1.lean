-- Prove2me | solution 1 for WilliamsonShmoys.subgraph_edgeFinset_card_mono__p2m_0c1d2833_de32_49c5_aebf_88ae0a9260a2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:04:55.802342+00:00
-- url     : https://prove2.me/submissions/c1928bdc-be4c-4db9-ac97-dda5716595a5

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hsub : G ≤ H) :
    G.edgeFinset.card ≤ H.edgeFinset.card := by
  exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hsub)