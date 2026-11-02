-- Prove2me | solution 1 for WilliamsonShmoys.finitePredicateHasInclusionMaximalSupergraph__p2m_58be6bd2_7b61_44ae_b8f6_153972a57451_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:37:23.91819+00:00
-- url     : https://prove2.me/submissions/c53ef42b-d6df-4ce0-8ac0-eef4eca18512

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (P : SimpleGraph V → Prop) (hP : P K) :
    ∃ (H : SimpleGraph V), K ≤ H ∧ P H ∧
      ∀ (J : SimpleGraph V), H ≤ J → P J → J ≤ H := by
  classical
  let S : Set (SimpleGraph V) := {H | K ≤ H ∧ P H}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨K, le_rfl, hP⟩
  obtain ⟨H, hHmax⟩ := hSfinite.exists_maximal hSnonempty
  refine ⟨H, hHmax.1.1, hHmax.1.2, ?_⟩
  intro J hHJ hPJ
  have hJmem : J ∈ S := ⟨hHmax.1.1.trans hHJ, hPJ⟩
  exact hHmax.2 hJmem hHJ