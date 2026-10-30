-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_strict_of_lt__p2m_4f8ddee9_6bbc_42a8_909b_77c7ff633307_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:04:08.068054+00:00
-- url     : https://prove2.me/submissions/dafa146e-0fb7-4d2b-959a-da30f2c6d7a3

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (h : G < H) :
    G.edgeSet.ncard < H.edgeSet.ncard := by
  exact Set.ncard_lt_ncard ((SimpleGraph.edgeSet_ssubset_edgeSet).2 h) (Set.toFinite H.edgeSet)