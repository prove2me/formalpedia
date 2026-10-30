-- Prove2me | solution 1 for WilliamsonShmoys.ordered_adj_card_le_universe__p2m_6dfe235c_2d93_4cd3_a1e8_c2011cbaaa57_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:29:56.444988+00:00
-- url     : https://prove2.me/submissions/e6c980c3-ec5d-4e7b-99dc-deb15a9b0d6f

import Mathlib

theorem solution {V : Type} [Fintype V] (G : SimpleGraph V) :
    Nat.card {p : V × V // G.Adj p.1 p.2} ≤ Nat.card (V × V) := by
  exact Nat.card_le_card_of_injective (fun p : {p : V × V // G.Adj p.1 p.2} => p.1)
    Subtype.val_injective