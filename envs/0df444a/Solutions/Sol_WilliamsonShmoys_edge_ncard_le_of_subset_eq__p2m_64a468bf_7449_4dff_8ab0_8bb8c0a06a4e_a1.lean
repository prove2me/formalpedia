-- Prove2me | solution 1 for WilliamsonShmoys.edge_ncard_le_of_subset_eq__p2m_64a468bf_7449_4dff_8ab0_8bb8c0a06a4e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:46:34.058857+00:00
-- url     : https://prove2.me/submissions/c212d3f5-432d-4cb0-835c-765dc087b1c0

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hSub : G.edgeSet ⊆ H.edgeSet)
    (hCount : H.edgeSet.ncard = 3 * Fintype.card V - 6) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  calc
    G.edgeSet.ncard ≤ H.edgeSet.ncard :=
      Set.ncard_le_ncard hSub (Set.toFinite H.edgeSet)
    _ = 3 * Fintype.card V - 6 := hCount