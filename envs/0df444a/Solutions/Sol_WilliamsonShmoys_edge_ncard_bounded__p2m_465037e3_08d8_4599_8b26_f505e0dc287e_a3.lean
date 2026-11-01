-- Prove2me | solution 1 for WilliamsonShmoys.edge_ncard_bounded__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:12:39.818113+00:00
-- url     : https://prove2.me/submissions/815162e1-bdd2-4a4a-bc04-9d53b98a6a61

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G : SimpleGraph V) :
    G.edgeSet.ncard ≤ Fintype.card (Sym2 V) := by
  simpa only [Nat.card_eq_fintype_card] using G.edgeSet.ncard_le_card