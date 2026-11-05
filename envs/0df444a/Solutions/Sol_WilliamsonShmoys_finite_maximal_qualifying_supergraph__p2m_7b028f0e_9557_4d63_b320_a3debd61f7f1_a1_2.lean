-- Prove2me | solution 2 for WilliamsonShmoys.finite_maximal_qualifying_supergraph__p2m_7b028f0e_9557_4d63_b320_a3debd61f7f1_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T18:40:19.672166+00:00
-- url     : https://prove2.me/submissions/7a84d633-7413-4f25-9ed8-ca8cfdbd09dc

import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hP : P G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧
      ∀ H' : SimpleGraph V, G ≤ H' → P H' → ¬ H < H' := by
  classical
  let p : SimpleGraph V → Prop := fun H => G ≤ H ∧ P H
  have hpG : p G := ⟨le_rfl, hP⟩
  obtain ⟨H, _hGH, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := G) hpG)
  rcases hmax with ⟨hpH, hmax'⟩
  refine ⟨H, hpH.1, hpH.2, ?_⟩
  intro H' hGH' hPH' hlt
  have hpH' : p H' := ⟨hGH', hPH'⟩
  have hH'H : H' ≤ H := hmax' hpH' (le_of_lt hlt)
  exact (not_lt_of_ge hH'H) hlt
