-- Prove2me | solution 1 for ValuationSubring.exists_ringHom_comap_fixedField_inertiaSubgroupIn_inf_fixingSubgroup_comp_eq_and_isDiscreteValuationRing_and_map_maximalIdeal_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/d2b78529-298d-5ffd-98f7-15eb9a86ea28

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn_inf_fixingSubgroup_and_exists_mul_of_mem_maximalIdeal
import Theorems.Thm_ValuationSubring_exists_residue_algebraMap_fixedField_inertiaSubgroupIn_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_ringHom_comap_fixedField_inertiaSubgroupIn_inf_fixingSubgroup_comp_eq_and_isDiscreteValuationRing_and_map_maximalIdeal_eq
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois"

set_option autoImplicit false

open IsLocalRing

theorem solution
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ)) :
    ∃ (ι : ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ))) →+* ↥Pl)
      (ρO : A →+* ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ)))),
      (∀ o : ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ))),
        ((ι o : ↥Pl) : AlgebraicClosure ℚ) = algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ) (o : ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)))) ∧
      ι.comp ρO = ρ ∧
      Function.Injective ι ∧
      IsDiscreteValuationRing ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ))) ∧
      Ideal.map ρO (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ))) ∧
      (∀ o : ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ))), ι o ∈ IsLocalRing.maximalIdeal ↥Pl ↔ o ∈ IsLocalRing.maximalIdeal ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ)))) ∧
      Function.Surjective (fun o : ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ))) => IsLocalRing.residue ↥Pl (ι o)) ∧
      (∀ σ ∈ Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup,
        ∀ o : ↥(Pl.comap (algebraMap ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup)) (AlgebraicClosure ℚ))), σ ((ι o : ↥Pl) : AlgebraicClosure ℚ) = ((ι o : ↥Pl) : AlgebraicClosure ℚ)) := by
  classical

  let H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    Pl.inertiaSubgroupIn ℚ ⊓ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup
  let F := IntermediateField.fixedField H
  let f : ↥F →+* AlgebraicClosure ℚ := algebraMap (↥F) (AlgebraicClosure ℚ)
  let O := Pl.comap f
  have hf : Function.Injective f := (algebraMap (↥F) (AlgebraicClosure ℚ)).injective

  have hρa : ∀ a : A, ((ρ a : ↥Pl) : AlgebraicClosure ℚ) = algebraMap A (AlgebraicClosure ℚ) a :=
    fun a => congrArg (fun g => g a) hρ
  have hAPl : ∀ a : A, algebraMap A (AlgebraicClosure ℚ) a ∈ Pl := fun a => hρa a ▸ (ρ a).2

  obtain ⟨hDVR, hover, hunr⟩ :=
    ValuationSubring.isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn_inf_fixingSubgroup_and_exists_mul_of_mem_maximalIdeal
      p L A hAp Pl hPl hAPl

  let ι : ↥O →+* ↥Pl := (f.comp O.subtype).codRestrict Pl fun o => o.2
  have hι : ∀ o : ↥O, ((ι o : ↥Pl) : AlgebraicClosure ℚ) = f o := fun o => rfl

  have hAF : ∀ a : A, algebraMap A (AlgebraicClosure ℚ) a ∈ F := by
    intro a
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have hσL : σ ∈ (IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup := hσ.2
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσL
    apply hσL
    rw [IsScalarTower.algebraMap_apply A L (AlgebraicClosure ℚ)]
    exact ⟨algebraMap A L a, rfl⟩
  let ρO : A →+* ↥O :=
    { toFun := fun a => ⟨⟨algebraMap A (AlgebraicClosure ℚ) a, hAF a⟩, by
        change f ⟨algebraMap A (AlgebraicClosure ℚ) a, hAF a⟩ ∈ Pl
        exact hAPl a⟩
      map_one' := by apply Subtype.ext; apply Subtype.ext; simp
      map_mul' := fun x y => by apply Subtype.ext; apply Subtype.ext; simp
      map_zero' := by apply Subtype.ext; apply Subtype.ext; simp
      map_add' := fun x y => by apply Subtype.ext; apply Subtype.ext; simp }
  have hρO : ∀ a : A, (((ρO a : ↥O) : ↥F) : AlgebraicClosure ℚ) = algebraMap A (AlgebraicClosure ℚ) a := fun a => rfl

  have hnon : ∀ o : ↥O, o ∈ IsLocalRing.maximalIdeal ↥O ↔ f o ∈ Pl.nonunits := by
    intro o
    rw [← ValuationSubring.coe_mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
      ValuationSubring.mem_comap, map_inv₀, map_eq_zero_iff f hf]
  refine ⟨ι, ρO, hι, ?_, ?_, hDVR, ?_, ?_, ?_, ?_⟩
  ·
    ext a
    exact (hρa a).symm
  ·
    intro o o' h
    apply Subtype.ext
    apply hf
    exact congrArg (fun a : ↥Pl => (a : AlgebraicClosure ℚ)) h
  ·
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, hnon]
      exact hover a ha
    · intro o ho
      obtain ⟨a, o', ha, heq⟩ := hunr o ho
      have : o = ρO a * o' := by
        apply Subtype.ext; apply Subtype.ext
        rw [heq]; rfl
      rw [this]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)
  ·
    intro o
    rw [hnon, ← ValuationSubring.coe_mem_nonunits_iff, hι]
  ·
    intro x
    obtain ⟨y, hy⟩ := Pl.exists_residue_algebraMap_fixedField_inertiaSubgroupIn_eq hPl x
    have hyF : ((y : ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ))) : AlgebraicClosure ℚ) ∈ F := by
      rw [IntermediateField.mem_fixedField_iff]
      intro σ hσ
      exact (IntermediateField.mem_fixedField_iff _ _).mp
        (y : ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ))).2 σ hσ.1
    refine ⟨⟨⟨_, hyF⟩, y.2⟩, ?_⟩
    exact hy
  ·
    intro σ hσ o
    rw [hι]
    exact (IntermediateField.mem_fixedField_iff _ _).mp (o : ↥F).2 σ hσ

end S_ValuationSubring_exists_ringHom_comap_fixedField_inertiaSubgroupIn_inf_fixingSubgroup_comp_eq_and_isDiscreteValuationRing_and_map_maximalIdeal_eq
end P2MW
export P2MW.S_ValuationSubring_exists_ringHom_comap_fixedField_inertiaSubgroupIn_inf_fixingSubgroup_comp_eq_and_isDiscreteValuationRing_and_map_maximalIdeal_eq (solution)
