-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_supergraph__p2m_abbad492_aa2c_464e_8cb6_154e5e3bb3de_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:44:47.056295+00:00
-- url     : https://prove2.me/submissions/bbe7a472-7e97-476a-a1b5-130fdb82f0b8

import Mathlib

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (H : SimpleGraph V)
    (hP : P H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ P K ∧
      (∀ L : SimpleGraph V, K ≤ L → P L → L = K) := by
  let p : SimpleGraph V → Prop := fun K => H ≤ K ∧ P K
  have hpH : p H := ⟨le_rfl, hP⟩
  obtain ⟨K, hHK, hKmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := H) hpH)
  rcases hKmax with ⟨hKp, hKmax'⟩
  refine ⟨K, hKp.1, hKp.2, ?_⟩
  intro L hKL hPL
  exact le_antisymm (hKmax' ⟨hKp.1.trans hKL, hPL⟩ hKL) hKL
