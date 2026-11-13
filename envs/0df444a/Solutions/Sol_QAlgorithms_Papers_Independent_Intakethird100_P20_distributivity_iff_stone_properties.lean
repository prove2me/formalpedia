-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.distributivity_iff_stone_properties
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-13T03:11:55.236843+00:00
-- url     : https://prove2.me/submissions/e1b30417-f351-4391-8e88-b436dd06d20a

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_stone_topology_properties
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_orthomodular_basic_sets_injective
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_distributive_basic_unions
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_stone_boolean_representation
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_upward_and_meet_closed
import Mathlib.Topology.Sets.Closeds
set_option autoImplicit false

open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace


open scoped Topology

universe u v

/-- Proposition 3.5; de Groote, Observables I, PDF p./pp. 44.
-/
theorem solution {L : Type u} [Lattice L] [BoundedOrder L] (perp : L → L)
    (horth : IsOrthomodular perp) :
    (IsDistributive (L := L) ↔ ∀ a b : L, stoneBasic a ∪ stoneBasic b = stoneBasic (a ⊔ b)) ∧
    (IsDistributive (L := L) ↔ ∀ a : L, stoneBasic a ∪ stoneBasic (perp a) = Set.univ) ∧
    (IsDistributive (L := L) ↔ ∀ s : Set (StoneSpectrum L), IsClopen s → ∃ a : L, s = stoneBasic a) := by
  classical
  have hp := horth.1
  have ht := stone_topology_properties (L := L)
  have hinj : Function.Injective (stoneBasic : L → Set (StoneSpectrum L)) :=
    fun a b he => orthomodular_basic_sets_injective perp horth he
  have hpinj : Function.Injective perp := fun a b he => by
    have hh := congrArg perp he
    simpa only [hp.2.2] using hh
  have hunions : IsDistributive (L := L) ↔
      ∀ a b : L, stoneBasic a ∪ stoneBasic b = stoneBasic (a ⊔ b) := by
    refine ⟨distributive_basic_unions.1,?_⟩
    intro hh
    have hi (a b c : L) : a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c) :=
      (hinj (distributive_basic_unions.2 hh a b c)).symm
    refine ⟨hi,?_⟩
    intro a b c
    apply hpinj
    rw [(hp.2.1 a (b ⊓ c)).2,(hp.2.1 b c).1,
      (hp.2.1 (a ⊔ b) (a ⊔ c)).1,(hp.2.1 a b).2,(hp.2.1 a c).2]
    exact hi (perp a) (perp b) (perp c)
  have hcovers : IsDistributive (L := L) ↔
      ∀ a : L, stoneBasic a ∪ stoneBasic (perp a) = Set.univ := by
    constructor
    · intro hd a
      rw [hunions.mp hd a (perp a),(hp.1 a).2]
      exact ht.2.2.1
    · intro hh
      apply hunions.mpr
      intro a b
      ext B
      have hu := quasipoint_upward_and_meet_closed B.val B.property
      change (a ∈ B.val ∨ b ∈ B.val) ↔ a ⊔ b ∈ B.val
      constructor
      · rintro (ha | hb)
        · exact hu.1 a ha _ le_sup_left
        · exact hu.1 b hb _ le_sup_right
      · intro hab
        by_cases ha : a ∈ B.val
        · exact Or.inl ha
        · by_cases hb : b ∈ B.val
          · exact Or.inr hb
          · have hc (x : L) : x ∈ B.val ∨ perp x ∈ B.val := by
              change B ∈ stoneBasic x ∪ stoneBasic (perp x)
              rw [hh]
              trivial
            have hpa := (hc a).resolve_left ha
            have hpb := (hc b).resolve_left hb
            have hpp := hu.2 (perp a) hpa (perp b) hpb
            rw [← (hp.2.1 a b).2] at hpp
            have hz := hu.2 (a ⊔ b) hab (perp (a ⊔ b)) hpp
            rw [(hp.1 (a ⊔ b)).1] at hz
            exact False.elim (B.property.1.2.1 hz)
  refine ⟨hunions,hcovers,?_⟩
  constructor
  · intro hd
    letI : BooleanAlgebra L :=
      { (inferInstance : Lattice L),(inferInstance : BoundedOrder L) with
        compl := perp
        le_sup_inf := fun a b c => le_of_eq (hd.2 a b c).symm
        inf_compl_le_bot := fun a => le_of_eq (hp.1 a).1
        top_le_sup_compl := fun a => le_of_eq (hp.1 a).2.symm }
    obtain ⟨e,he⟩ := (stone_boolean_representation (L := L)).2.2.2
    intro s hs
    let C : Clopens (StoneSpectrum L) := ⟨s,hs⟩
    refine ⟨e.symm C,?_⟩
    rw [← he,e.apply_symm_apply]
    rfl
  · intro hh
    apply hunions.mpr
    have ho {a b : L} (hsub : stoneBasic a ⊆ stoneBasic b) : a ≤ b := by
      apply inf_eq_left.mp
      apply hinj
      rw [ht.1,Set.inter_eq_left.mpr hsub]
    intro a b
    obtain ⟨c,hc⟩ := hh (stoneBasic a ∪ stoneBasic b)
      ((ht.2.2.2.1 a).union (ht.2.2.2.1 b))
    have hac : a ≤ c := ho (by rw [← hc]; exact Set.subset_union_left)
    have hbc : b ≤ c := ho (by rw [← hc]; exact Set.subset_union_right)
    have hcab : c ≤ a ⊔ b := by
      apply ho
      rw [← hc]
      intro B hB
      have hu := quasipoint_upward_and_meet_closed B.val B.property
      rcases hB with ha | hb
      · exact hu.1 a ha (a ⊔ b) le_sup_left
      · exact hu.1 b hb (a ⊔ b) le_sup_right
    have heq : c = a ⊔ b := le_antisymm hcab (sup_le hac hbc)
    simpa only [heq] using hc
