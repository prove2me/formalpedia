-- Prove2me | solution 1 for WilliamsonShmoys.finite_property_maximal_extension__p2m_b6765847_4b48_4473_801c_ad92c775fb51_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T18:42:20.589402+00:00
-- url     : https://prove2.me/submissions/535115de-ac8c-45a0-86fa-69706162f87c

import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

theorem solution {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (N : SimpleGraph V)
    (hN : P N) :
    ∃ H : SimpleGraph V,
      N ≤ H ∧
      P H ∧
      N.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ K : SimpleGraph V,
        H ≤ K → P K → K ≤ H) := by
  classical
  let p : SimpleGraph V → Prop := fun H => P H ∧ N ≤ H
  have hpN : p N := ⟨hN, le_rfl⟩
  obtain ⟨H, _hNH, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := N) hpN)
  rcases hmax with ⟨hpH, hmax'⟩
  have hsub : N.edgeSet ⊆ H.edgeSet := SimpleGraph.edgeSet_subset_edgeSet.mpr hpH.2
  have hfin : H.edgeSet.Finite := Set.toFinite _
  refine ⟨H, hpH.2, hpH.1, Set.ncard_le_ncard hsub hfin, ?_⟩
  intro K hHK hPK
  exact hmax' ⟨hPK, hpH.2.trans hHK⟩ hHK
