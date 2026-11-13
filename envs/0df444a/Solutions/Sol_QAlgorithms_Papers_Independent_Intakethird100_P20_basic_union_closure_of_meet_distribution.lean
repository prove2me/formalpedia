-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.basic_union_closure_of_meet_distribution
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T16:17:34.292979+00:00
-- url     : https://prove2.me/submissions/0b225150-0daa-4b5a-9181-19b5350f4b46

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_stone_topology_properties
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_closure_of_basic_union
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_upward_and_meet_closed
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Intakethird100.P20

theorem solution {L : Type*} [CompleteLattice L]
    (s : Set L) (hdistrib : ∀ b : L, b ⊓ sSup s = sSup ((fun a => b ⊓ a) '' s)) :
    closure (⋃ a ∈ s, stoneBasic a) = stoneBasic (sSup s) := by
  classical
  have ht := stone_topology_properties (L := L)
  have hu := quasipoint_upward_and_meet_closed (L := L)
  apply Set.Subset.antisymm
  · apply closure_minimal
    · intro B hB
      obtain ⟨a, ha, hBa⟩ := Set.mem_iUnion₂.mp hB
      exact (hu B.val B.property).1 a hBa (sSup s) (le_sSup ha)
    · exact (ht.2.2.2.1 (sSup s)).1
  · intro B hB
    apply (closure_of_basic_union s B).mpr
    intro b hb
    by_contra hn
    have hall : ∀ a ∈ s, b ⊓ a = ⊥ := by
      intro a ha
      by_contra hh
      exact hn ⟨a, ha, hh⟩
    have hz : sSup ((fun a => b ⊓ a) '' s) = (⊥ : L) := by
      apply le_antisymm _ bot_le
      apply sSup_le
      rintro _ ⟨a, ha, rfl⟩
      exact le_of_eq (hall a ha)
    have hh := (hu B.val B.property).2 b hb (sSup s) hB
    rw [hdistrib b, hz] at hh
    exact B.property.1.2.1 hh
