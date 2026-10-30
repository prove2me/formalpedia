-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_mono__p2m_b94ddc87_8e35_451a_9f65_e1e9d97b1c62_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:26:06.056792+00:00
-- url     : https://prove2.me/submissions/7dd01332-4674-4ce0-bc6d-c20c0f2d1fe3

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V)
    (hHK : H ≤ K) :
    H.edgeSet.ncard ≤ K.edgeSet.ncard := by
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hHK)