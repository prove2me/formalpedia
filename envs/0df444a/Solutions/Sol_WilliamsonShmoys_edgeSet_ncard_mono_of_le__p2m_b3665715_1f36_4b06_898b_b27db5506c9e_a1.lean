-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_mono_of_le__p2m_b3665715_1f36_4b06_898b_b27db5506c9e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:24:40.386453+00:00
-- url     : https://prove2.me/submissions/3529560d-5ccb-4da4-bb62-eb7320e23423

import Mathlib

theorem solution
    {V : Type} [Fintype V]
    {K G : SimpleGraph V}
    (hKG : K ≤ G) :
    K.edgeSet.ncard ≤ G.edgeSet.ncard := by
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hKG)