-- Prove2me | solution 1 for WilliamsonShmoys.edge_card_lt_of_le_of_ne__p2m_f100cac1_01af_43d8_b482_631795dea89f_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T17:53:58.183173+00:00
-- url     : https://prove2.me/submissions/483c202a-a181-4583-a0ca-0b2964f0cd72

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G H : SimpleGraph V)
    (hGH : G ≤ H) (hne : G ≠ H) :
    Nat.card {e : Sym2 V // e ∈ G.edgeSet} < Nat.card {e : Sym2 V // e ∈ H.edgeSet} := by
  classical
  change G.edgeSet.ncard < H.edgeSet.ncard
  have hlt : G < H := lt_of_le_of_ne hGH hne
  have hss : G.edgeSet ⊂ H.edgeSet :=
    (SimpleGraph.edgeSet_ssubset_edgeSet).2 hlt
  exact Set.ncard_lt_ncard hss (Set.toFinite _)
