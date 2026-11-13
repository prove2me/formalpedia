-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.isolated_quasipoint_iff_atom
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T16:39:10.018008+00:00
-- url     : https://prove2.me/submissions/241141bb-57d4-4de3-b317-c294486db899

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_stone_topology_properties
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_atom_principal_is_quasipoint
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_stoneBasic_nonempty_iff
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_orthomodular_basic_sets_injective
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_upward_and_meet_closed
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Proposition 3.6; de Groote, Observables I, PDF p./pp. 44.
-/
theorem solution {L : Type u} [Lattice L] [BoundedOrder L] (perp : L → L)
    (horth : IsOrthomodular perp) (B : StoneSpectrum L) :
    IsOpen ({B} : Set (StoneSpectrum L)) ↔
      ∃! a : L, IsAtom a ∧ B.val = principalQuasipoint a := by
  classical
  have ht := stone_topology_properties (L := L)
  have hp (a : L) (ha : IsAtom a) (C : StoneSpectrum L) (hac : a ∈ C.val) :
      C.val = principalQuasipoint a := by
    apply (atom_principal_is_quasipoint a ha).2 C.val C.property.1
    intro x hx
    exact (quasipoint_upward_and_meet_closed C.val C.property).1 a hac x hx
  constructor
  · intro hB
    obtain ⟨V, ⟨a, rfl⟩, hBa, hsub⟩ :=
      ht.2.2.2.2.1.exists_subset_of_mem_open (Set.mem_singleton B) hB
    have hQa : stoneBasic a = {B} :=
      Set.Subset.antisymm hsub (Set.singleton_subset_iff.mpr hBa)
    have ha : IsAtom a := by
      apply isAtom_iff_le_of_ge.mpr
      refine ⟨(stoneBasic_nonempty_iff a).mp ⟨B, hBa⟩, ?_⟩
      intro c hc0 hca
      have hsubc : stoneBasic c ⊆ stoneBasic a := by
        intro C hc
        exact (quasipoint_upward_and_meet_closed C.val C.property).1 c hc a hca
      obtain ⟨D, hDc⟩ := (stoneBasic_nonempty_iff c).mpr hc0
      have hDa := hsubc hDc
      rw [hQa] at hDa
      have hDB : D = B := hDa
      have hBc : B ∈ stoneBasic c := hDB ▸ hDc
      have heq : stoneBasic c = stoneBasic a :=
        Set.Subset.antisymm hsubc (hQa ▸ Set.singleton_subset_iff.mpr hBc)
      exact le_of_eq (orthomodular_basic_sets_injective perp horth heq).symm
    have hpr := hp a ha B hBa
    refine ⟨a, ⟨ha, hpr⟩, ?_⟩
    intro c hc
    have hcB : c ∈ B.val := by rw [hc.2]; exact le_rfl
    have hac : a ≤ c := by rw [hpr] at hcB; exact hcB
    have hca : c ≤ a := by
      have hmem : a ∈ B.val := hBa
      rw [hc.2] at hmem
      exact hmem
    exact le_antisymm hca hac
  · rintro ⟨a, ⟨ha, hpr⟩, _⟩
    have hBa : a ∈ B.val := by rw [hpr]; exact le_rfl
    have hQa : stoneBasic a = {B} := by
      apply Set.Subset.antisymm
      · intro C hc
        have hcpr := hp a ha C hc
        exact Set.mem_singleton_iff.mpr (Subtype.ext (hcpr.trans hpr.symm))
      · exact Set.singleton_subset_iff.mpr hBa
    rw [← hQa]
    exact (ht.2.2.2.1 a).2
