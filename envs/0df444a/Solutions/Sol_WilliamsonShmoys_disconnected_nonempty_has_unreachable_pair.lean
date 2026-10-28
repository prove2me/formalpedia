-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_nonempty_has_unreachable_pair
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T16:44:05.382115+00:00
-- url     : https://prove2.me/submissions/d8ab6e9a-73aa-4e0f-b034-5507f1cdd60b

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (hV : 0 < Fintype.card V)
    (hDisconnected : ¬ H.Connected) :
    ∃ u v : V, ¬ H.Reachable u v := by
  classical
  by_contra hNoPair
  push_neg at hNoPair
  letI : Nonempty V := Fintype.card_pos_iff.mp hV
  exact hDisconnected ⟨hNoPair⟩