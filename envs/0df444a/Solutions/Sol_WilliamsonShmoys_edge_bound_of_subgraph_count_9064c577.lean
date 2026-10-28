-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_of_subgraph_count_9064c577
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:22:37.228412+00:00
-- url     : https://prove2.me/submissions/af1d9b81-2aa4-4a3d-9432-dc290988622e

import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K H : SimpleGraph V)
    (hSub : K.edgeSet ⊆ H.edgeSet)
    (hCount : H.edgeSet.ncard + 6 = 3 * Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  have hle : K.edgeSet.ncard ≤ H.edgeSet.ncard := Set.ncard_le_ncard hSub
  omega