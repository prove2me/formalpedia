-- Prove2me | solution 1 for WilliamsonShmoys.exists_nonreachable_pair
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T01:54:33.507986+00:00
-- url     : https://prove2.me/submissions/ba86ce12-f2fc-4dac-b2a2-22c6713274a7

import Mathlib
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hdisc : ¬ H.Connected) : ∃ u v : V, u ≠ v ∧ ¬ H.Adj u v ∧ ¬ H.Reachable u v := by
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have : ¬ H.Preconnected := fun h => hdisc ⟨h⟩
  simp only [SimpleGraph.Preconnected, not_forall] at this
  obtain ⟨u, v, huv⟩ := this
  refine ⟨u, v, ?_, fun h => huv h.reachable, huv⟩
  rintro rfl; exact huv (SimpleGraph.Reachable.refl _)
