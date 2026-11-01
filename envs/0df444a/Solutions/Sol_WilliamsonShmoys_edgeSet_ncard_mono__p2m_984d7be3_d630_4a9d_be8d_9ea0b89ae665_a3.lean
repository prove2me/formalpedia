-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_mono__p2m_984d7be3_d630_4a9d_be8d_9ea0b89ae665_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:16:40.632775+00:00
-- url     : https://prove2.me/submissions/6df68b6a-c8e5-4671-aa29-d2397e5f8933

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (H K : SimpleGraph V) (hHK : H ≤ K) :
    H.edgeSet.ncard ≤ K.edgeSet.ncard := by
  exact Set.ncard_mono (SimpleGraph.edgeSet_mono hHK)