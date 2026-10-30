-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_mono__p2m_2727cf65_1722_4248_9cab_723efcbdd93a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:27:15.495593+00:00
-- url     : https://prove2.me/submissions/1d874d8c-6ff9-48f2-9eba-873465c3089b

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (G H : SimpleGraph V) (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGH)