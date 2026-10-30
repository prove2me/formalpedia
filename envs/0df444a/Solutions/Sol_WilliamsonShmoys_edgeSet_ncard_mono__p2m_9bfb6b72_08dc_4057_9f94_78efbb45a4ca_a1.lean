-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_mono__p2m_9bfb6b72_08dc_4057_9f94_78efbb45a4ca_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:21:30.569772+00:00
-- url     : https://prove2.me/submissions/dcaf7f4a-dc1b-4435-9d1b-3da013c90b4b

import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (K H : SimpleGraph V)
    (hKH : K ≤ H) :
    K.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hKH)