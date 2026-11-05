-- Prove2me | solution 1 for WilliamsonShmoys.finite_hereditary_property_maximal_supergraph__p2m_b1eaa68f_d3bc_482e_8876_be28beef9c21_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:44:56.348609+00:00
-- url     : https://prove2.me/submissions/49bc40c9-d273-48b7-89fa-93646d3f2204

import Mathlib

set_option linter.unusedVariables false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V → Prop)
    (hhered : ∀ A B : SimpleGraph V, A ≤ B → P B → P A) (G : SimpleGraph V) (hG : P G) :
    ∃ T : SimpleGraph V, G ≤ T ∧ P T ∧
      ∀ U : SimpleGraph V, T ≤ U → P U → U ≤ T := by
  classical
  let p : SimpleGraph V → Prop := fun T => P T ∧ G ≤ T
  have hpG : p G := ⟨hG, le_rfl⟩
  obtain ⟨T, hGT, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := G) hpG)
  rcases hmax with ⟨hpT, hmax'⟩
  refine ⟨T, hpT.2, hpT.1, ?_⟩
  intro U hTU hPU
  exact hmax' ⟨hPU, hGT.trans hTU⟩ hTU
