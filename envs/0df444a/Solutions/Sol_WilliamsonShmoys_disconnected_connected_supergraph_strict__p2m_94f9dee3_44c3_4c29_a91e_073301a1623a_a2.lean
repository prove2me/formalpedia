-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_connected_supergraph_strict__p2m_94f9dee3_44c3_4c29_a91e_073301a1623a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:46:45.709104+00:00
-- url     : https://prove2.me/submissions/31e3cdfe-6a6a-4b58-99ed-1fdec5f3da12

import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hHK : H.edgeFinset ⊆ K.edgeFinset)
    (hH : ¬ H.Connected)
    (hK : K.Connected) :
    H.edgeFinset ⊂ K.edgeFinset := by
  rw [SimpleGraph.edgeFinset_ssubset_edgeFinset]
  apply lt_of_le_of_ne
  · exact (SimpleGraph.edgeFinset_subset_edgeFinset).mp hHK
  · intro hEq
    apply hH
    simpa [hEq] using hK