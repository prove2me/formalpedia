-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_vertices_not_reachable__p2m_8ebe9775_f6af_4eb7_9344_68ad2c5d7599_a4
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T03:39:49.347866+00:00
-- url     : https://prove2.me/submissions/16c3a3e1-5b9a-4e79-b61f-8d5d71954b1d

import Mathlib

set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hDisconnected : ¬ N.Connected), ∃ u v : V, u ≠ v ∧ ¬ N.Reachable u v) := by
  intro claimed
  -- V = Fin 0: no graph on an empty type is connected, and no vertices exist.
  have hnc : ¬ (⊥ : SimpleGraph (Fin 0)).Connected := fun h => h.nonempty.elim fun x => x.elim0
  obtain ⟨u, _, _, _⟩ := claimed (V := Fin 0) ⊥ hnc
  exact u.elim0

#print axioms solution
