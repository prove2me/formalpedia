-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_monotone_4881293e_7bf5_4184_9f0b_57a8f75b0b6d
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:53:38.565188+00:00
-- url     : https://prove2.me/submissions/ea19b341-408d-44a7-b129-7216033109d5

import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L T : SimpleGraph V)
    (hLT : L ≤ T)
    (hT : T.edgeSet.ncard = 3 * Fintype.card V - 6) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  exact le_trans (Set.ncard_mono (SimpleGraph.edgeSet_mono hLT)) (le_of_eq hT)