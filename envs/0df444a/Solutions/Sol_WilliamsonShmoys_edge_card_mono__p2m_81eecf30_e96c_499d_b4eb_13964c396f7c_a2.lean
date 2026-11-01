-- Prove2me | solution 1 for WilliamsonShmoys.edge_card_mono__p2m_81eecf30_e96c_499d_b4eb_13964c396f7c_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:42:58.038029+00:00
-- url     : https://prove2.me/submissions/0f6bb7c8-583c-4a96-841c-c659b4181af1

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (hGH : G ≤ H) :
    letI : DecidableRel G.Adj := Classical.decRel _
    letI : DecidableRel H.Adj := Classical.decRel _
    G.edgeFinset.card ≤ H.edgeSet.ncard := by
  classical
  calc
    G.edgeFinset.card ≤ H.edgeFinset.card :=
      Finset.card_le_card (SimpleGraph.edgeFinset_mono hGH)
    _ = H.edgeSet.ncard := by
      simpa [SimpleGraph.edgeFinset] using
        (Set.ncard_eq_toFinset_card H.edgeSet).symm