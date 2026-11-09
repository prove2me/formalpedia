-- Prove2me | solution 1 for WilliamsonShmoys.exists_disconnected_partition__p2m_6eb1d1e9_05be_4cdb_8344_dedf44e2bf5b_a2
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T03:43:09.538842+00:00
-- url     : https://prove2.me/submissions/b31d4ff6-f479-41e8-bb62-642b263036a0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] (M : SimpleGraph V) (hdisc : ¬ M.Connected), ∃ A : Set V, A.Nonempty ∧ Aᶜ.Nonempty ∧ (∀ ⦃u v : V⦄, u ∈ A → v ∈ Aᶜ → ¬ M.Adj u v)) := by
  intro claimed
  -- V = Fin 0: no graph on an empty type is connected, and no subset of it is nonempty.
  have hnc : ¬ (⊥ : SimpleGraph (Fin 0)).Connected := fun h => h.nonempty.elim fun x => x.elim0
  obtain ⟨A, ⟨a, _⟩, _, _⟩ := claimed (V := Fin 0) ⊥ hnc
  exact a.elim0

#print axioms solution
