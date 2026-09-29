-- Prove2me | solution 1 for ValuationSubring.exists_normal_commutator_mem_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/c2866143-763d-5c12-be79-b4c62aef6d80

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_normal_commutator_mem_of_isDiscreteValuationRing

set_option autoImplicit false

universe u v

namespace S17C2

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
variable {A : ValuationSubring L}

theorem smul_sub_mem (σ : ↥(A.decompositionSubgroup K)) (hσ : σ ∈ A.inertiaSubgroup K) (a : ↥A) :
    σ • a - a ∈ IsLocalRing.maximalIdeal ↥A := by
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, IsLocalRing.ResidueField.residue_smul, sub_eq_zero]
  exact DFunLike.congr_fun (MonoidHom.mem_ker.mp hσ) (IsLocalRing.residue (↥A) a)

theorem residue_smul_eq (σ : ↥(A.decompositionSubgroup K)) (hσ : σ ∈ A.inertiaSubgroup K) (a : ↥A) :
    IsLocalRing.residue (↥A) (σ • a) = IsLocalRing.residue (↥A) a := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact smul_sub_mem σ hσ a

variable [IsDiscreteValuationRing ↥A]

theorem exists_mul_eq_smul (σ : ↥(A.decompositionSubgroup K)) {ϖ : ↥A} (hϖ : Irreducible ϖ) :
    ∃ u : ↥A, u * ϖ = σ • ϖ := by
  have hmem : σ • ϖ ∈ IsLocalRing.maximalIdeal ↥A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hϖ.not_isUnit
    have h := hu.map (MulSemiringAction.toRingHom (↥(A.decompositionSubgroup K)) (↥A) σ⁻¹)
    rwa [MulSemiringAction.toRingHom_apply, inv_smul_smul] at h
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ] at hmem
  exact Ideal.mem_span_singleton'.mp hmem

section Theta

variable (K A)
variable {ϖ : ↥A} (hϖ : Irreducible ϖ)

noncomputable def U (σ : ↥(A.decompositionSubgroup K)) : ↥A := (exists_mul_eq_smul σ hϖ).choose

theorem U_spec (σ : ↥(A.decompositionSubgroup K)) : U K A hϖ σ * ϖ = σ • ϖ := (exists_mul_eq_smul σ hϖ).choose_spec

include hϖ in
theorem U_mul (σ τ : ↥(A.decompositionSubgroup K)) : U K A hϖ (σ * τ) = σ • U K A hϖ τ * U K A hϖ σ := by
  have hne : ϖ ≠ 0 := hϖ.ne_zero
  apply mul_right_cancel₀ hne
  rw [U_spec, mul_smul, ← U_spec K A hϖ τ, smul_mul', ← U_spec K A hϖ σ, mul_assoc]

theorem U_one : U K A hϖ 1 = 1 := by
  have hne : ϖ ≠ 0 := hϖ.ne_zero
  apply mul_right_cancel₀ hne
  rw [U_spec, one_smul, one_mul]

noncomputable def theta : ↥(A.inertiaSubgroup K) →* IsLocalRing.ResidueField ↥A where
  toFun σ := IsLocalRing.residue (↥A) (U K A hϖ (σ : ↥(A.decompositionSubgroup K)))
  map_one' := by
    show IsLocalRing.residue (↥A) (U K A hϖ 1) = 1
    rw [U_one, map_one]
  map_mul' σ τ := by
    show IsLocalRing.residue (↥A) (U K A hϖ ((σ : ↥(A.decompositionSubgroup K)) * τ)) = _
    rw [U_mul, map_mul, residue_smul_eq _ σ.2, mul_comm]

theorem theta_apply (σ : ↥(A.inertiaSubgroup K)) :
    theta K A hϖ σ = IsLocalRing.residue (↥A) (U K A hϖ (σ : ↥(A.decompositionSubgroup K))) := rfl

theorem theta_eq_one_iff (σ : ↥(A.inertiaSubgroup K)) :
    theta K A hϖ σ = 1 ↔ ((σ : ↥(A.decompositionSubgroup K)) • ϖ - ϖ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A ^ 2 := by
  have hspan : IsLocalRing.maximalIdeal ↥A = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hkey : ((σ : ↥(A.decompositionSubgroup K)) • ϖ - ϖ : ↥A) = (U K A hϖ σ - 1) * ϖ := by
    rw [sub_mul, one_mul, U_spec]
  rw [theta_apply, ← (IsLocalRing.residue (↥A)).map_one, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, hkey, pow_two]
  constructor
  · intro h
    exact Ideal.mul_mem_mul h (hspan ▸ Ideal.mem_span_singleton_self ϖ)
  · intro h
    rw [hspan, Ideal.span_singleton_mul_span_singleton, Ideal.mem_span_singleton'] at h
    obtain ⟨c, hc⟩ := h
    rw [hspan, Ideal.mem_span_singleton']
    exact ⟨c, mul_right_cancel₀ hϖ.ne_zero (by rw [mul_assoc, hc])⟩

theorem smul_sub_mem_sq_of_theta_eq_one (σ : ↥(A.inertiaSubgroup K)) (h : theta K A hϖ σ = 1)
    (ϖ' : ↥A) (hϖ' : Irreducible ϖ') :
    ((σ : ↥(A.decompositionSubgroup K)) • ϖ' - ϖ' : ↥A) ∈ IsLocalRing.maximalIdeal ↥A ^ 2 := by
  have hspan : IsLocalRing.maximalIdeal ↥A = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ

  have hmem : ϖ' ∈ Ideal.span {ϖ} := by
    rw [← hspan, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hϖ'.not_isUnit
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.mp hmem
  have hU : U K A hϖ σ - 1 ∈ IsLocalRing.maximalIdeal ↥A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_one, sub_eq_zero]
    exact h
  have hw : (σ : ↥(A.decompositionSubgroup K)) • w - w ∈ IsLocalRing.maximalIdeal ↥A := smul_sub_mem _ σ.2 w
  have hcalc : ((σ : ↥(A.decompositionSubgroup K)) • (w * ϖ) - w * ϖ : ↥A)
      = (((σ : ↥(A.decompositionSubgroup K)) • w - w) * U K A hϖ σ + w * (U K A hϖ σ - 1)) * ϖ := by
    rw [smul_mul', ← U_spec K A hϖ]
    ring
  rw [hcalc, pow_two]
  refine Ideal.mul_mem_mul ?_ (hspan ▸ Ideal.mem_span_singleton_self ϖ)
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hw) (Ideal.mul_mem_left _ _ hU)

end Theta

end S17C2

open S17C2 in
theorem solution
    (K : Type u) [Field K] {L : Type v} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (A : ValuationSubring L) [IsDiscreteValuationRing ↥A] :
    ∃ Pw : Subgroup ↥(A.inertiaSubgroup K),
      (∀ σ : ↥(A.inertiaSubgroup K), σ ∈ Pw ↔
        ∀ ϖ : ↥A, Irreducible ϖ →
          ((σ : ↥(A.decompositionSubgroup K)) • ϖ - ϖ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A ^ 2) ∧
      Pw.Normal ∧ ∀ a b : ↥(A.inertiaSubgroup K), a⁻¹ * b⁻¹ * a * b ∈ Pw := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥A
  let θ := theta K A hϖ
  refine ⟨θ.ker, fun σ => ?_, ?_, fun a b => ?_⟩
  · rw [MonoidHom.mem_ker]
    constructor
    · intro h ϖ' hϖ'
      exact smul_sub_mem_sq_of_theta_eq_one K A hϖ σ h ϖ' hϖ'
    · intro h
      exact (theta_eq_one_iff K A hϖ σ).mpr (h ϖ hϖ)
  · refine ⟨fun n hn g => ?_⟩
    rw [MonoidHom.mem_ker] at hn ⊢
    rw [map_mul, map_mul, hn, mul_one, ← map_mul, mul_inv_cancel, map_one]
  · rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul]
    calc θ a⁻¹ * θ b⁻¹ * θ a * θ b = (θ a⁻¹ * θ a) * (θ b⁻¹ * θ b) := by ring
      _ = 1 := by rw [← map_mul, ← map_mul, inv_mul_cancel, inv_mul_cancel, map_one, one_mul]

end S_ValuationSubring_exists_normal_commutator_mem_of_isDiscreteValuationRing
end P2MW
export P2MW.S_ValuationSubring_exists_normal_commutator_mem_of_isDiscreteValuationRing (solution)
