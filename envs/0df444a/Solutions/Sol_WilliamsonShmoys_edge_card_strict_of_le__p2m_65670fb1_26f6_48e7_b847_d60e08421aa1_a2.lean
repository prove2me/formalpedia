-- Prove2me | solution 1 for WilliamsonShmoys.edge_card_strict_of_le__p2m_65670fb1_26f6_48e7_b847_d60e08421aa1_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:03:44.303598+00:00
-- url     : https://prove2.me/submissions/34b55157-c7fd-400b-82b9-af244f6f5de2

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (H K : SimpleGraph V)
    (hHK : H ≤ K)
    (hne : H ≠ K) :
    H.edgeSet.ncard < K.edgeSet.ncard := by
  apply Set.ncard_lt_ncard
  · rw [Set.ssubset_iff_subset_ne]
    constructor
    · exact SimpleGraph.edgeSet_subset_edgeSet.mpr hHK
    · intro hEq
      exact hne (SimpleGraph.edgeSet_inj.mp hEq)
  · exact Set.toFinite _