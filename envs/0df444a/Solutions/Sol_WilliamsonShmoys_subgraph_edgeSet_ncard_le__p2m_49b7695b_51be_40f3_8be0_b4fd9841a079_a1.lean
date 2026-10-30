-- Prove2me | solution 1 for WilliamsonShmoys.subgraph_edgeSet_ncard_le__p2m_49b7695b_51be_40f3_8be0_b4fd9841a079_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:25:30.57493+00:00
-- url     : https://prove2.me/submissions/026e65a9-f708-4754-b116-9110ac7044aa

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (K H : SimpleGraph V)
    (hKH : K ≤ H) :
    K.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact Set.ncard_mono (SimpleGraph.edgeSet_mono hKH)