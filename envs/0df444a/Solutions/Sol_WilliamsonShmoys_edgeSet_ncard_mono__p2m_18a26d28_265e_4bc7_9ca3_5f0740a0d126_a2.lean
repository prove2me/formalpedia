-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_mono__p2m_18a26d28_265e_4bc7_9ca3_5f0740a0d126_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:09:34.191672+00:00
-- url     : https://prove2.me/submissions/56ad10ec-b8e1-40fd-b2b4-863928debb19

import Mathlib
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (X Y : SimpleGraph V) (hXY : X ≤ Y) :
    X.edgeSet.ncard ≤ Y.edgeSet.ncard := by
  exact Set.ncard_mono (SimpleGraph.edgeSet_mono hXY)