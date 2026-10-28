-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_disconnected_has_nonadjacent_pair
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:08:59.80607+00:00
-- url     : https://prove2.me/submissions/8c310c70-5d49-40c0-9ba8-0ea85eaa61a4

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ H.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ H.Reachable u v ∧ ¬ H.Adj u v := by
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hpre : ¬ H.Preconnected := fun h => hDisconnected ⟨h⟩
  simp only [SimpleGraph.Preconnected, not_forall] at hpre
  obtain ⟨u, v, huv⟩ := hpre
  refine ⟨u, v, ?_, huv, fun h => huv h.reachable⟩
  rintro rfl
  exact huv (SimpleGraph.Reachable.refl u)
