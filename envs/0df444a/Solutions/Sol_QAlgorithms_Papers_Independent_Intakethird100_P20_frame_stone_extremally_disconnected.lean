-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.frame_stone_extremally_disconnected
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T16:20:13.876396+00:00
-- url     : https://prove2.me/submissions/3a2028ec-d613-4269-8148-85d758a0881d

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_basic_union_closure_of_meet_distribution
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_stone_topology_properties
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Proposition 3.7; de Groote, Observables I, PDF p./pp. 45.
-/
theorem solution {L : Type u} [CompleteLattice L] (hframe : HasFrameLaw L) :
    ExtremallyDisconnected (StoneSpectrum L) ∧
      ∀ s : Set L, closure (⋃ a ∈ s, stoneBasic a) = stoneBasic (sSup s) := by
  classical
  have ht := stone_topology_properties (L := L)
  have hb := ht.2.2.2.2.1
  have hclose (s : Set L) : closure (⋃ a ∈ s, stoneBasic a) = stoneBasic (sSup s) :=
    basic_union_closure_of_meet_distribution s (fun b => hframe b s)
  refine ⟨⟨?_⟩, hclose⟩
  intro U hU
  let s : Set L := {a | stoneBasic a ⊆ U}
  have heq : (⋃ a ∈ s, stoneBasic a) = U := by
    apply Set.Subset.antisymm
    · intro B hB
      obtain ⟨a, ha, hb⟩ := Set.mem_iUnion₂.mp hB
      exact ha hb
    · intro B hB
      obtain ⟨V, ⟨a, rfl⟩, hBa, hsub⟩ := hb.exists_subset_of_mem_open hB hU
      exact Set.mem_iUnion₂.mpr ⟨a, hsub, hBa⟩
  rw [← heq, hclose]
  exact (ht.2.2.2.1 (sSup s)).2
