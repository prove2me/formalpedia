-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_mono_cd050b01_9a07_4b9b_9132_918bb6a60ec5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:13:47.137618+00:00
-- url     : https://prove2.me/submissions/354bd5cc-33e6-40b5-acaa-3933a004e3c6

import Mathlib

theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (h : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact Set.ncard_mono ((SimpleGraph.edgeSetEmbedding V).monotone h)