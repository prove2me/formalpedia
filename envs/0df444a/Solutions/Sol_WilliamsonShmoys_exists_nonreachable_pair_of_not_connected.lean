-- Prove2me | solution 1 for WilliamsonShmoys.exists_nonreachable_pair_of_not_connected
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:37:26.394808+00:00
-- url     : https://prove2.me/submissions/685d64c6-310a-4340-a55f-30b58077c4b3

import Mathlib

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ G.Connected) :
    ∃ u v : V, ¬ G.Reachable u v := by
  by_contra h
  push_neg at h
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  exact hDisconnected ⟨fun u v => h u v⟩
