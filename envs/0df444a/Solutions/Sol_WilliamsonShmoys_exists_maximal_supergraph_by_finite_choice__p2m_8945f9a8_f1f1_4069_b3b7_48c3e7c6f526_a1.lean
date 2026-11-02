-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_by_finite_choice__p2m_8945f9a8_f1f1_4069_b3b7_48c3e7c6f526_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:58:11.598208+00:00
-- url     : https://prove2.me/submissions/ea1eca10-4e0d-46b2-97dc-f12bc4d0babd

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (Q : SimpleGraph V → Prop)
    (hP : Q P) :
    ∃ H : SimpleGraph V,
      P ≤ H ∧
      Q H ∧
      (∀ K : SimpleGraph V, Q K → H ≤ K → K ≤ H) := by
  classical
  let admissible : Set (SimpleGraph V) := {K | P ≤ K ∧ Q K}
  have hfinite : admissible.Finite := Set.toFinite admissible
  obtain ⟨H, hH, hmax⟩ := hfinite.exists_maximal ⟨P, le_rfl, hP⟩
  refine ⟨H, hH.1, hH.2, ?_⟩
  intro K hK hHK
  exact hmax ⟨hH.1.trans hHK, hK⟩ hHK