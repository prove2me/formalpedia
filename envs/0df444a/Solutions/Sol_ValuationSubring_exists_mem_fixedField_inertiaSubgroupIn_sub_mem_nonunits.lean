-- Prove2me | solution 1 for ValuationSubring.exists_mem_fixedField_inertiaSubgroupIn_sub_mem_nonunits
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/188c6e2a-0f28-52cf-9741-45ebf6ead54c

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_residue_algebraMap_fixedField_inertiaSubgroupIn_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_mem_fixedField_inertiaSubgroupIn_sub_mem_nonunits

set_option autoImplicit false

namespace ResidueSurj

open scoped Pointwise in

theorem mem_inertiaSubgroupIn_iff_forall {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (σ : L ≃ₐ[K] L) :
    σ ∈ A.inertiaSubgroupIn K ↔
      (∀ x : L, σ.symm x ∈ A ↔ x ∈ A) ∧ ∀ a : L, a ∈ A → σ a - a ∈ A.nonunits := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    have hstab : (d : L ≃ₐ[K] L) • A = A := d.2
    refine ⟨fun x => ?_, fun a ha => ?_⟩
    · conv_rhs => rw [← hstab]
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      rfl
    · have hker : MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A) d = 1 := hd
      have h1 : d • IsLocalRing.residue A ⟨a, ha⟩ = IsLocalRing.residue A ⟨a, ha⟩ := by
        have := RingEquiv.congr_fun hker (IsLocalRing.residue A ⟨a, ha⟩)
        simpa using this
      rw [← IsLocalRing.ResidueField.residue_smul] at h1
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff] at h1
      have h2 := ValuationSubring.coe_mem_nonunits_iff.mpr h1
      simp at h2
      exact h2
  · rintro ⟨hA, hres⟩
    have hstab : σ • A = A := by
      ext x
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      exact hA x
    refine ⟨⟨σ, hstab⟩, ?_, rfl⟩
    change MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A) ⟨σ, hstab⟩ = 1
    apply RingEquiv.ext
    intro r
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
    change (⟨σ, hstab⟩ : A.decompositionSubgroup K) • IsLocalRing.residue A a = IsLocalRing.residue A a
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    apply ValuationSubring.coe_mem_nonunits_iff.mp
    have h__af := hres a a.2
    simp at h__af ⊢
    exact h__af

theorem mem_inertiaSubgroupIn_iff_of_forall_apply_eq
    {K E L : Type*} [Field K] [Field E] [Field L] [Algebra K L] [Algebra E L]
    (A : ValuationSubring L) (σ : L ≃ₐ[K] L) (τ : L ≃ₐ[E] L) (h : ∀ x : L, σ x = τ x) :
    σ ∈ A.inertiaSubgroupIn K ↔ τ ∈ A.inertiaSubgroupIn E := by
  have hsymm : ∀ x : L, σ.symm x = τ.symm x := fun x => by
    apply τ.injective
    rw [← h, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  rw [mem_inertiaSubgroupIn_iff_forall, mem_inertiaSubgroupIn_iff_forall]
  simp only [hsymm, h]

end ResidueSurj

theorem solution
    (F : Type) [Field F] [NumberField F] [Algebra F (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ) [Fact q.Prime] (hP : P.LiesOverPrime q)
    (a : AlgebraicClosure ℚ) (ha : a ∈ P) :
    ∃ c : AlgebraicClosure ℚ, c ∈ IntermediateField.fixedField (P.inertiaSubgroupIn F) ∧ c ∈ P ∧
      ∃ h : a - c ∈ P, (⟨a - c, h⟩ : ↥P) ∈ IsLocalRing.maximalIdeal ↥P := by
  classical

  obtain ⟨y, hy⟩ := ValuationSubring.exists_residue_algebraMap_fixedField_inertiaSubgroupIn_eq P hP
    (IsLocalRing.residue ↥P ⟨a, ha⟩)
  have hcP : ((y : ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))) : AlgebraicClosure ℚ) ∈ P := y.2
  refine ⟨((y : ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))) : AlgebraicClosure ℚ), ?_, hcP, ?_⟩
  ·
    rw [IntermediateField.mem_fixedField_iff]
    intro τ hτ
    have hy2 := (y : ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))).2
    rw [IntermediateField.mem_fixedField_iff] at hy2
    let σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) (fun r => by simp)
    have hσ : σ ∈ P.inertiaSubgroupIn ℚ :=
      (ResidueSurj.mem_inertiaSubgroupIn_iff_of_forall_apply_eq P σ τ (fun _ => rfl)).mpr hτ
    exact hy2 σ hσ
  · refine ⟨P.toSubring.sub_mem ha hcP, ?_⟩
    rw [← IsLocalRing.residue_eq_zero_iff]
    have hsub : (⟨a - _, P.toSubring.sub_mem ha hcP⟩ : ↥P) = ⟨a, ha⟩ - ⟨_, hcP⟩ := rfl
    rw [hsub, map_sub, sub_eq_zero]
    exact hy.symm

end S_ValuationSubring_exists_mem_fixedField_inertiaSubgroupIn_sub_mem_nonunits
end P2MW
export P2MW.S_ValuationSubring_exists_mem_fixedField_inertiaSubgroupIn_sub_mem_nonunits (solution)
