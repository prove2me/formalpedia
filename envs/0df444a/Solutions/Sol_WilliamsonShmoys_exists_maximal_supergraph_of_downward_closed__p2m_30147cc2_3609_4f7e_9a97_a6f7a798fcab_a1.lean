-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_of_downward_closed__p2m_30147cc2_3609_4f7e_9a97_a6f7a798fcab_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T17:22:09.400848+00:00
-- url     : https://prove2.me/submissions/63eca04e-e7b7-4fe0-88f7-c40a2766b474

import Mathlib

set_option linter.unusedVariables false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ ⦃A B : SimpleGraph V⦄, A ≤ B → P B → P A)
    (G : SimpleGraph V) (hG : P G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ P H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ K : SimpleGraph V, H ≤ K → P K → K ≤ H) := by
  classical
  let p : SimpleGraph V → Prop := fun H => P H ∧ G ≤ H
  have hpG : p G := ⟨hG, le_rfl⟩
  obtain ⟨H, hGH, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := G) hpG)
  rcases hmax with ⟨hpH, hmax'⟩
  have hsub : G.edgeSet ⊆ H.edgeSet := SimpleGraph.edgeSet_subset_edgeSet.mpr hGH
  refine ⟨H, hGH, hpH.1, Set.ncard_le_ncard hsub (Set.toFinite _), ?_⟩
  intro K hHK hPK
  exact hmax' ⟨hPK, hGH.trans hHK⟩ hHK
