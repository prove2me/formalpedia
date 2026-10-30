-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_mono__p2m_ecceac01_0239_445e_a0b3_a366a9290cdc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:44:11.17784+00:00
-- url     : https://prove2.me/submissions/12c8ffed-ef20-4e2a-94d4-050a4ef53c75

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (G H : SimpleGraph V) (h : G ≤ H) : G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact Set.ncard_mono (SimpleGraph.edgeSet_subset_edgeSet.mpr h)