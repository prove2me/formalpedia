-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_has_nonadjacent_vertices
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T09:39:55.522932+00:00
-- url     : https://prove2.me/submissions/395660c8-c570-4ee6-b7fe-013331639c7d

import Mathlib
set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ X.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ X.Adj u v := by
  by_contra h
  push_neg at h
  apply hDisconnected
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  refine ⟨fun u v => ?_⟩
  by_cases huv : u = v
  · subst huv; rfl
  · exact (h u v huv).reachable
