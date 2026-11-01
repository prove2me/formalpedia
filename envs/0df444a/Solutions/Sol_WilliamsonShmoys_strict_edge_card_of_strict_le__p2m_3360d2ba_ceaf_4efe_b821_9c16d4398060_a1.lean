-- Prove2me | solution 1 for WilliamsonShmoys.strict_edge_card_of_strict_le__p2m_3360d2ba_ceaf_4efe_b821_9c16d4398060_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:25:42.820709+00:00
-- url     : https://prove2.me/submissions/87bebd6e-27d0-4cb1-9362-cd5b8370c132

import Mathlib
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    {G K : SimpleGraph V} (hGK : G ≤ K) (hne : G ≠ K) :
    Nat.card {e : Sym2 V // e ∈ G.edgeSet} <
      Nat.card {e : Sym2 V // e ∈ K.edgeSet} := by
  have hlt : G < K := lt_of_le_of_ne hGK hne
  simpa only [Nat.card_coe_set_eq] using
    (Set.ncard_lt_ncard (SimpleGraph.edgeSet_ssubset_edgeSet.mpr hlt))