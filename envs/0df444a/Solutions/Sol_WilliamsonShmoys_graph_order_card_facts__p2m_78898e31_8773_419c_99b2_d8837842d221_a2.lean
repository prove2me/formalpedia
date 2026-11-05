-- Prove2me | solution 1 for WilliamsonShmoys.graph_order_card_facts__p2m_78898e31_8773_419c_99b2_d8837842d221_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:42:06.946524+00:00
-- url     : https://prove2.me/submissions/f112a14c-353e-48f9-a27b-b6304b06c3a5

import Mathlib

theorem solution
    {V : Type} [Fintype V]
    (M N : SimpleGraph V) (hMN : M ≤ N) :
    M.edgeSet.ncard ≤ N.edgeSet.ncard ∧
      (M.edgeSet.ncard = N.edgeSet.ncard → M = N) := by
  classical
  have hsub : M.edgeSet ⊆ N.edgeSet := SimpleGraph.edgeSet_subset_edgeSet.mpr hMN
  have hfin : N.edgeSet.Finite := Set.toFinite _
  constructor
  · exact Set.ncard_le_ncard hsub hfin
  · intro heq
    apply SimpleGraph.edgeSet_inj.mp
    exact Set.eq_of_subset_of_ncard_le hsub (by omega) hfin
