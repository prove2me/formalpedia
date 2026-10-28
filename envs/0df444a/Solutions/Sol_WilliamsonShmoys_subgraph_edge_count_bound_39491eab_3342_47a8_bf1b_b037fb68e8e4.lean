-- Prove2me | solution 1 for WilliamsonShmoys.subgraph_edge_count_bound_39491eab_3342_47a8_bf1b_b037fb68e8e4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:25:54.657113+00:00
-- url     : https://prove2.me/submissions/5a7169f5-4b20-437f-9f61-375bfe8b7af7

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (H K : SimpleGraph V)
    (hHK : H ≤ K)
    (hK : K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  have hcard : H.edgeSet.ncard ≤ K.edgeSet.ncard :=
    Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hHK)
  calc
    H.edgeSet.ncard + 6 ≤ K.edgeSet.ncard + 6 := Nat.add_le_add_right hcard 6
    _ ≤ 3 * Fintype.card V := hK