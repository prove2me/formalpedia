-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.atom_principal_is_quasipoint
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T16:34:42.115426+00:00
-- url     : https://prove2.me/submissions/efb95d71-cfbe-48b6-a122-3164222e4ef2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

open QAlgorithms.Papers.Independent.Intakethird100.P20

theorem solution {L : Type*} [Lattice L] [BoundedOrder L]
    (a : L) (ha : IsAtom a) : IsQuasipoint (principalQuasipoint a) := by
  classical
  have hbase : IsFilterBase (principalQuasipoint a) := by
    refine ⟨⟨a, le_rfl⟩, ?_, ?_⟩
    · intro h
      exact ha.ne_bot (le_bot_iff.mp h)
    · intro x hx y hy
      exact ⟨a, le_rfl, hx, hy⟩
  refine ⟨hbase, ?_⟩
  intro C hC hsub
  apply Set.Subset.antisymm _ hsub
  intro x hx
  have hac : a ∈ C := hsub le_rfl
  obtain ⟨c, hc, hca, hcx⟩ := hC.2.2 a hac x hx
  have hc0 : c ≠ ⊥ := fun hz => hC.2.1 (hz ▸ hc)
  have heq : c = a := (ha.le_iff_eq hc0).mp hca
  change a ≤ x
  exact heq ▸ hcx
