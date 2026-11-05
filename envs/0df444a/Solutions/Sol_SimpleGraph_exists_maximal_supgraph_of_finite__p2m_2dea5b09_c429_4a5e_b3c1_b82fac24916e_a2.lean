-- Prove2me | solution 1 for SimpleGraph.exists_maximal_supgraph_of_finite__p2m_2dea5b09_c429_4a5e_b3c1_b82fac24916e_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:46:15.203233+00:00
-- url     : https://prove2.me/submissions/c3299631-9abe-4543-9909-04a03c5de9ac

import Mathlib

set_option linter.unusedVariables false

theorem solution
    {V : Type} [Fintype V] (P : SimpleGraph V → Prop)
    (hdown : ∀ ⦃G H : SimpleGraph V⦄, H ≤ G → P G → P H)
    (K : SimpleGraph V) (hK : P K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ P L ∧
      ∀ M : SimpleGraph V, L ≤ M → P M  → M ≤ L := by
  classical
  let p : SimpleGraph V → Prop := fun X => K ≤ X ∧ P X
  have hpK : p K := ⟨le_rfl, hK⟩
  obtain ⟨L, hKL, hLmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := K) hpK)
  refine ⟨L, hKL, hLmax.1.2, ?_⟩
  intro M hLM hPM
  exact hLmax.2 ⟨hKL.trans hLM, hPM⟩ hLM
