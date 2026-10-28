-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_has_unreachable_pair_e285668e
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T02:02:15.226188+00:00
-- url     : https://prove2.me/submissions/068ab5df-cbde-4425-ba3f-29cab04b635e

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDisconnected : ¬ L.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ u v : V, u ≠ v ∧ ¬ L.Reachable u v := by
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hp : ¬ L.Preconnected := fun h => hDisconnected ⟨h⟩
  simp only [SimpleGraph.Preconnected, not_forall] at hp
  obtain ⟨u, v, h⟩ := hp
  exact ⟨u, v, fun e => h (e ▸ SimpleGraph.Reachable.refl u), h⟩
