-- Prove2me | solution 1 for WilliamsonShmoys.eq_of_le_ncard__p2m_184d0625_bb96_4aaf_8936_3881fc188830_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:02:40.704215+00:00
-- url     : https://prove2.me/submissions/326be1a4-21f4-4b87-8e4b-d4b6e35a67fa

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V)
    (hHK : H ≤ K)
    (hcard : K.edgeSet.ncard ≤ H.edgeSet.ncard) :
    K = H := by
  classical
  have hsets : H.edgeSet = K.edgeSet :=
    Set.eq_of_subset_of_ncard_le (SimpleGraph.edgeSet_mono hHK) hcard
  exact (SimpleGraph.edgeSet_injective hsets).symm