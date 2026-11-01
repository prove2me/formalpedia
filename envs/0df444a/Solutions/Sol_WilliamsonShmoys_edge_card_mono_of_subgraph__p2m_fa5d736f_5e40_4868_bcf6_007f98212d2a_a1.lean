-- Prove2me | solution 1 for WilliamsonShmoys.edge_card_mono_of_subgraph__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:19:10.394101+00:00
-- url     : https://prove2.me/submissions/0aeb3d57-3d32-4a79-b15f-4c1dd784a4fb

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (H K : SimpleGraph V)
    (hHK : H ≤ K) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    H.edgeFinset.card ≤ K.edgeFinset.card := by
  classical
  exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hHK)