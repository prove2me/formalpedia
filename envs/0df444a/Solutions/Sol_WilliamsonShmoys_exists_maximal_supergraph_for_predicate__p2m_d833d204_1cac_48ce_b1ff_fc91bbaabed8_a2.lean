-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_for_predicate__p2m_d833d204_1cac_48ce_b1ff_fc91bbaabed8_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:56:11.900204+00:00
-- url     : https://prove2.me/submissions/2d38c0fe-e3b5-41ab-be30-80ba4a350ee9

import Mathlib

set_option autoImplicit false

open SimpleGraph

/-- A predicate on finite simple graphs has a maximal qualifying extension of any
qualifying graph. -/
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (L : SimpleGraph V) (hL : P L) :
    ∃ H : SimpleGraph V, L ≤ H ∧ P H ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by
  classical
  let Q : SimpleGraph V → Prop := fun G => L ≤ G ∧ P G
  have hQ : ∃ G : SimpleGraph V, Q G := ⟨L, le_rfl, hL⟩
  obtain ⟨H, _hHdec, hHext⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists Q).2 hQ
  have hHq : Q H := hHext.prop
  refine ⟨H, hHq.1, hHq.2, ?_⟩
  intro K hHK hPK
  have hKq : Q K := ⟨hHq.1.trans hHK, hPK⟩
  have hEq : H = K := (hHext.le_iff_eq hKq).mp hHK
  exact hEq.symm