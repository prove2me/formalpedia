-- Prove2me | solution 1 for WilliamsonShmoys.eq_of_extension_edge_card_bound__p2m_07b78964_cbaf_4bb7_98dc_a4ce7ae0f70a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:11:10.942762+00:00
-- url     : https://prove2.me/submissions/1e5b41cb-0441-4937-a298-7f96c84b69d9

import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N K : SimpleGraph V)
    (hNK : N ≤ K)
    (hCard : K.edgeSet.ncard ≤ N.edgeSet.ncard) :
    K = N := by
  have hEdges : N.edgeSet = K.edgeSet :=
    Set.eq_of_subset_of_ncard_le
      (SimpleGraph.edgeSet_subset_edgeSet.mpr hNK)
      hCard
  exact SimpleGraph.edgeSet_inj.mp hEdges.symm