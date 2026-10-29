-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_simpleGraph_property_extension__p2m_2d2efbeb_7ceb_4fa3_8371_f356ba71853f_a1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:10:11.859314+00:00
-- url     : https://prove2.me/submissions/2a8911fc-b03e-4b70-9abb-28b283b18d97

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (T : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hT : P T) :
    ∃ R : SimpleGraph V,
      (∀ u v, T.Adj u v → R.Adj u v) ∧
      P R ∧
      (∀ S : SimpleGraph V,
        (∀ u v, T.Adj u v → S.Adj u v) →
        P S →
        (∀ u v, R.Adj u v → S.Adj u v) → S = R) := by
  obtain ⟨R, -, hR⟩ := Finite.exists_le_maximal (p := fun S : SimpleGraph V => T ≤ S ∧ P S)
    (a := T) ⟨le_rfl, hT⟩
  refine ⟨R, fun u v h => hR.1.1 h, hR.1.2, fun S hTS hPS hRS => ?_⟩
  have h1 : R ≤ S := fun u v h => hRS u v h
  exact le_antisymm (hR.2 ⟨fun u v h => hTS u v h, hPS⟩ h1) h1
