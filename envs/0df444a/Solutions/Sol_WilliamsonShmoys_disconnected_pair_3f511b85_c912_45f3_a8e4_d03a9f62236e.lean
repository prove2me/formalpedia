-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_pair_3f511b85_c912_45f3_a8e4_d03a9f62236e
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T15:38:21.701202+00:00
-- url     : https://prove2.me/submissions/ef1f1583-140b-4b0d-a42f-f7e261191b18

import Mathlib

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 2 <= Fintype.card V)
    (hDisconnected : ¬ G.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ G.Reachable u v := by
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hpre : ¬ G.Preconnected := fun h => hDisconnected ⟨h⟩
  simp only [SimpleGraph.Preconnected, not_forall] at hpre
  obtain ⟨u, v, h⟩ := hpre
  exact ⟨u, v, by rintro rfl; exact h (SimpleGraph.Reachable.refl u), h⟩
