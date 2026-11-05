-- Prove2me | solution 1 for WilliamsonShmoys.finite_property_has_maximal_supergraph__p2m_e39dc392_ef53_43de_92b9_a9ba96581299_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:43:53.910266+00:00
-- url     : https://prove2.me/submissions/8b82897e-5bca-4391-be0e-5b0d34a5c187

import Mathlib

set_option linter.unusedVariables false

theorem solution
    {V : Type} [Fintype V]
    (N : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hdown : ∀ ⦃A B : SimpleGraph V⦄, A ≤ B → P B → P A)
    (hN : P N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ P K ∧
        ∀ L : SimpleGraph V, K ≤ L → P L → L = K := by
  classical
  let p : SimpleGraph V → Prop := fun K => P K ∧ N ≤ K
  have hpN : p N := ⟨hN, le_rfl⟩
  obtain ⟨K, hNK, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := N) hpN)
  rcases hmax with ⟨hpK, hmax'⟩
  refine ⟨K, hpK.2, hpK.1, ?_⟩
  intro L hKL hPL
  have hpL : p L := ⟨hPL, hNK.trans hKL⟩
  exact (le_antisymm hKL (hmax' hpL hKL)).symm
