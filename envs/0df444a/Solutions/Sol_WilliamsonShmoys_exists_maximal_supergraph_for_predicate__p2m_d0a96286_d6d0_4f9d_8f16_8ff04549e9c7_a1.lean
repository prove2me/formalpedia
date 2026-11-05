-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_for_predicate__p2m_d0a96286_d6d0_4f9d_8f16_8ff04549e9c7_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T18:43:22.716198+00:00
-- url     : https://prove2.me/submissions/dae8c3df-ab2d-45a3-8d38-f085fe7606b5

import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

theorem solution {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (H : SimpleGraph V)
    (hH : P H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      P K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet →
        P L →
        L.edgeSet ⊆ K.edgeSet := by
  classical
  let p : SimpleGraph V → Prop := fun K => P K ∧ H ≤ K
  have hpH : p H := ⟨hH, le_rfl⟩
  obtain ⟨K, _hHK, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := H) hpH)
  rcases hmax with ⟨hpK, hmax'⟩
  have hsub : H.edgeSet ⊆ K.edgeSet :=
    SimpleGraph.edgeSet_subset_edgeSet.mpr hpK.2
  refine ⟨K, hsub, hpK.1, ?_⟩
  intro L hKL hPL
  have hKLle : K ≤ L := SimpleGraph.edgeSet_subset_edgeSet.mp hKL
  have hpL : p L := ⟨hPL, hpK.2.trans hKLle⟩
  have hLKle : L ≤ K := hmax' hpL hKLle
  exact SimpleGraph.edgeSet_subset_edgeSet.mpr hLKle
