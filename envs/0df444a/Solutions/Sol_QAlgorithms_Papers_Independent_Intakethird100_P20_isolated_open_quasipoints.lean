-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.isolated_open_quasipoints
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T16:48:17.823001+00:00
-- url     : https://prove2.me/submissions/9c337ecc-e952-4b3f-9706-cc1d4a081b26

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_stone_topology_properties
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_atom_principal_is_quasipoint
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_open_atom_iff_singleton
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_stoneBasic_nonempty_iff
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_upward_and_meet_closed
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- atomic-open-quasipoints; de Groote, Observables I, PDF p./pp. 44, 45.
-/
theorem solution {M : Type u} [TopologicalSpace M] [T2Space M] (B : StoneSpectrum (Opens M)) :
    (IsOpen ({B} : Set (StoneSpectrum (Opens M))) ↔
      ∃! U : Opens M, IsAtom U ∧ B.val = principalQuasipoint U) ∧
    (IsOpen ({B} : Set (StoneSpectrum (Opens M))) ↔
      ∃! x : M, IsOpen ({x} : Set M) ∧ B.val = {U : Opens M | x ∈ (U : Set M)}) := by
  classical
  have ht := stone_topology_properties (L := Opens M)
  have hp (U : Opens M) (ha : IsAtom U) (C : StoneSpectrum (Opens M)) (hac : U ∈ C.val) :
      C.val = principalQuasipoint U := by
    apply (atom_principal_is_quasipoint U ha).2 C.val C.property.1
    intro V hUV
    exact (quasipoint_upward_and_meet_closed C.val C.property).1 U hac V hUV
  have huniq (U : Opens M) (heq : B.val = principalQuasipoint U)
      (V : Opens M) (hV : B.val = principalQuasipoint V) : V = U := by
    have hUB : U ∈ B.val := by rw [heq]; exact le_refl U
    have hVB : V ∈ B.val := by rw [hV]; exact le_refl V
    apply le_antisymm
    · rw [hV] at hUB; exact hUB
    · rw [heq] at hVB; exact hVB
  have hAB : IsOpen ({B} : Set (StoneSpectrum (Opens M))) ↔
      ∃! U : Opens M, IsAtom U ∧ B.val = principalQuasipoint U := by
    constructor
    · intro hB
      obtain ⟨_, ⟨U, rfl⟩, hBU, hsub⟩ :=
        ht.2.2.2.2.1.exists_subset_of_mem_open (Set.mem_singleton B) hB
      have hsmall (V : Opens M) (hv : V ≠ ⊥) (hVU : V ≤ U) : V ∈ B.val := by
        obtain ⟨C, hc⟩ := (stoneBasic_nonempty_iff V).mpr hv
        have hcU := (quasipoint_upward_and_meet_closed C.val C.property).1 V hc U hVU
        have hCB : C = B := Set.mem_singleton_iff.mp (hsub hcU)
        exact hCB ▸ hc
      have hU0 : U ≠ ⊥ := (stoneBasic_nonempty_iff U).mp ⟨B, hBU⟩
      obtain ⟨x, hx⟩ := (Opens.ne_bot_iff_nonempty U).mp hU0
      have hUx : (U : Set M) = {x} := by
        apply Set.Subset.antisymm _ (Set.singleton_subset_iff.mpr hx)
        intro y hy
        by_contra hyx
        have hxy : x ≠ y := fun he => hyx (Set.mem_singleton_iff.mpr he.symm)
        obtain ⟨v, w, hv, hw, hxv, hyw, hvw⟩ := t2_separation hxy
        let V : Opens M := U ⊓ ⟨v, hv⟩
        let W : Opens M := U ⊓ ⟨w, hw⟩
        have hvB := hsmall V ((Opens.ne_bot_iff_nonempty V).mpr ⟨x, hx, hxv⟩) inf_le_left
        have hwB := hsmall W ((Opens.ne_bot_iff_nonempty W).mpr ⟨y, hy, hyw⟩) inf_le_left
        have hz : V ⊓ W = ⊥ := by
          apply SetLike.coe_injective
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro z hz
          exact Set.disjoint_left.mp hvw hz.1.2 hz.2.2
        have hbot := (quasipoint_upward_and_meet_closed B.val B.property).2 V hvB W hwB
        exact B.property.1.2.1 (hz ▸ hbot)
      have ha : IsAtom U := (open_atom_iff_singleton U).mpr ⟨x, hUx⟩
      have heq := hp U ha B hBU
      exact ⟨U, ⟨ha, heq⟩, fun V hV => huniq U heq V hV.2⟩
    · rintro ⟨U, ⟨ha, heq⟩, _⟩
      have hBU : U ∈ B.val := by rw [heq]; exact le_refl U
      have hQ : stoneBasic U = {B} := by
        apply Set.Subset.antisymm
        · intro C hc
          exact Set.mem_singleton_iff.mpr (Subtype.ext ((hp U ha C hc).trans heq.symm))
        · exact Set.singleton_subset_iff.mpr hBU
      rw [← hQ]
      exact (ht.2.2.2.1 U).2
  have hBC : (∃! U : Opens M, IsAtom U ∧ B.val = principalQuasipoint U) ↔
      ∃! x : M, IsOpen ({x} : Set M) ∧ B.val = {U : Opens M | x ∈ (U : Set M)} := by
    constructor
    · rintro ⟨U, ⟨ha, heq⟩, _⟩
      obtain ⟨x, hUx⟩ := (open_atom_iff_singleton U).mp ha
      have hxopen : IsOpen ({x} : Set M) := hUx ▸ U.isOpen
      have hpoint : B.val = {V : Opens M | x ∈ (V : Set M)} := by
        ext V
        rw [heq]
        change ((U : Set M) ⊆ (V : Set M)) ↔ x ∈ (V : Set M)
        rw [hUx]
        exact Set.singleton_subset_iff
      refine ⟨x, ⟨hxopen, hpoint⟩, ?_⟩
      intro y hy
      have hUB : U ∈ B.val := by rw [heq]; exact le_refl U
      rw [hy.2] at hUB
      change y ∈ (U : Set M) at hUB
      rw [hUx] at hUB
      exact hUB
    · rintro ⟨x, ⟨hxopen, hpoint⟩, _⟩
      let U : Opens M := ⟨{x}, hxopen⟩
      have ha : IsAtom U := (open_atom_iff_singleton U).mpr ⟨x, rfl⟩
      have heq : B.val = principalQuasipoint U := by
        ext V
        rw [hpoint]
        change (x ∈ (V : Set M)) ↔ ({x} ⊆ (V : Set M))
        exact Set.singleton_subset_iff.symm
      exact ⟨U, ⟨ha, heq⟩, fun V hV => huniq U heq V hV.2⟩
  exact ⟨hAB, hAB.trans hBC⟩
