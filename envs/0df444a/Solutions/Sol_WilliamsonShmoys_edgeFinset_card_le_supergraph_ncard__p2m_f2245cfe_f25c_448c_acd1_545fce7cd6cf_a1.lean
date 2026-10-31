-- Prove2me | solution 1 for WilliamsonShmoys.edgeFinset_card_le_supergraph_ncard__p2m_f2245cfe_f25c_448c_acd1_545fce7cd6cf_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:24:46.150265+00:00
-- url     : https://prove2.me/submissions/b0355213-770a-45f8-a73b-6185eb0e614a

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (hGH : G ≤ H) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     G.edgeFinset.card) ≤ H.edgeSet.ncard := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  rw [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard]
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGH)