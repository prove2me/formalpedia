-- Prove2me | solution 1 for WilliamsonShmoys.exists_separating_cut_of_not_connected
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T05:09:45.386132+00:00
-- url     : https://prove2.me/submissions/01b14f1e-7f4b-46bb-a279-16185d1efb52

import Mathlib

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ K.Connected) :
    ∃ A : Set V, A.Nonempty ∧ Aᶜ.Nonempty ∧
      ∀ ⦃x y : V⦄, x ∈ A → y ∉ A → ¬ K.Adj x y := by
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hpre : ¬ K.Preconnected := fun h => hDisconnected ⟨h⟩
  simp only [SimpleGraph.Preconnected, not_forall] at hpre
  obtain ⟨u, v, huv⟩ := hpre
  refine ⟨{x | K.Reachable u x}, ⟨u, SimpleGraph.Reachable.refl u⟩, ⟨v, huv⟩, ?_⟩
  intro x y hx hy hxy
  exact hy (hx.trans hxy.reachable)
