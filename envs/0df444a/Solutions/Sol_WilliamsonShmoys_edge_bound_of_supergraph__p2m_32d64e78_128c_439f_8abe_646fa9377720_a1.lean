-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_of_supergraph__p2m_32d64e78_128c_439f_8abe_646fa9377720_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:11:47.641174+00:00
-- url     : https://prove2.me/submissions/b86d60b4-8069-4681-94e6-4cf29960d35a

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V)
    (hHK : H ≤ K)
    (hK : K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  have h_edges : H.edgeSet.ncard ≤ K.edgeSet.ncard :=
    Set.ncard_mono (SimpleGraph.edgeSet_mono hHK)
  exact (Nat.add_le_add_right h_edges 6).trans hK