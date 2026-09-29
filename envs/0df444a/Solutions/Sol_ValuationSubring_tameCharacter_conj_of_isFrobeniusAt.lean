-- Prove2me | solution 1 for ValuationSubring.tameCharacter_conj_of_isFrobeniusAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/c954897a-fe65-5198-aafd-8fa66a23963c

import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ValuationSubring_valuation_map_eq_of_mem_decompositionSubgroup
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_tameCharacter_conj_of_isFrobeniusAt

namespace DichTameRows

open ValuationSubring
open scoped Pointwise

variable (P : ValuationSubring (AlgebraicClosure ℚ))

private theorem tameCharacter_of_mem (π : AlgebraicClosure ℚ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (h : σ π / π ∈ P) : P.tameCharacter π σ = IsLocalRing.residue P ⟨σ π / π, h⟩ := by
  unfold ValuationSubring.tameCharacter
  exact dif_pos h

private theorem apply_mem_of_mem_decompositionSubgroup {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ P.decompositionSubgroup ℚ) {x : AlgebraicClosure ℚ} (hx : x ∈ P) : σ x ∈ P := by
  have h : σ • P = P := MulAction.mem_stabilizer_iff.mp hσ
  have hmem : σ • x ∈ ((σ • P : ValuationSubring (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ)) := by
    rw [coe_pointwise_smul]
    exact Set.smul_mem_smul_set hx
  rw [h] at hmem
  exact hmem

private theorem mem_decompositionSubgroup_of_mem_inertiaSubgroupIn {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) : σ ∈ P.decompositionSubgroup ℚ := by
  obtain ⟨σ', _, rfl⟩ := Subgroup.mem_map.mp hσ
  exact σ'.2

private theorem residue_apply_eq_of_mem_inertiaSubgroupIn {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) {x : AlgebraicClosure ℚ} (hx : x ∈ P)
    (hσx : σ x ∈ P) :
    IsLocalRing.residue P ⟨σ x, hσx⟩ = IsLocalRing.residue P ⟨x, hx⟩ := by
  obtain ⟨σ', hσ', rfl⟩ := Subgroup.mem_map.mp hσ
  have hker : MulSemiringAction.toRingAut (P.decompositionSubgroup ℚ) (IsLocalRing.ResidueField P) σ' = 1 :=
    (MonoidHom.mem_ker).mp hσ'
  have h1 : (MulSemiringAction.toRingAut (P.decompositionSubgroup ℚ) (IsLocalRing.ResidueField P) σ')
      (IsLocalRing.residue P ⟨x, hx⟩) = IsLocalRing.residue P ⟨x, hx⟩ := by
    rw [hker]
    rfl

  have h2 : IsLocalRing.residue P (σ' • (⟨x, hx⟩ : P)) = IsLocalRing.residue P ⟨x, hx⟩ := h1
  have hact : (σ' • (⟨x, hx⟩ : P) : P) = ⟨(P.decompositionSubgroup ℚ).subtype σ' x, hσx⟩ := Subtype.ext rfl
  rw [hact] at h2
  exact h2

private theorem apply_div_mem_of_mem_decompositionSubgroup {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ P.decompositionSubgroup ℚ) {x : AlgebraicClosure ℚ} (hx : x ≠ 0) :
    σ x / x ∈ P ∧ x / σ x ∈ P := by
  have hv := ValuationSubring.valuation_map_eq_of_mem_decompositionSubgroup P hσ x
  have hx' : P.valuation x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  refine ⟨(P.valuation_le_one_iff _).mp (le_of_eq ?_), (P.valuation_le_one_iff _).mp (le_of_eq ?_)⟩
  · rw [map_div₀, hv, div_self hx']
  · rw [map_div₀, hv, div_self hx']

private theorem tameCharacter_eq_of_div_mem_of_div_mem (π π' : AlgebraicClosure ℚ) (hπ : π ≠ 0) (hπ' : π' ≠ 0)
    (hu : π' / π ∈ P) (hu' : π / π' ∈ P) {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) :
    P.tameCharacter π' σ = P.tameCharacter π σ := by
  have hσD : σ ∈ P.decompositionSubgroup ℚ := mem_decompositionSubgroup_of_mem_inertiaSubgroupIn P hσ
  have hσπ : σ π / π ∈ P := (apply_div_mem_of_mem_decompositionSubgroup P hσD hπ).1
  have hσu : σ (π' / π) ∈ P := apply_mem_of_mem_decompositionSubgroup P hσD hu
  have hσπ0 : σ π ≠ 0 := (map_ne_zero σ).mpr hπ
  have hcoc : σ π' / π' = (σ (π' / π) * (π / π')) * (σ π / π) := by
    rw [map_div₀]
    field_simp
  have hmem : σ π' / π' ∈ P := by
    rw [hcoc]
    exact mul_mem (mul_mem hσu hu') hσπ
  rw [tameCharacter_of_mem P π' σ hmem, tameCharacter_of_mem P π σ hσπ]
  have hprod : (⟨σ π' / π', hmem⟩ : P) = (⟨σ (π' / π), hσu⟩ * ⟨π / π', hu'⟩) * ⟨σ π / π, hσπ⟩ :=
    Subtype.ext (by simpa only [MulMemClass.coe_mul] using hcoc)
  rw [hprod, map_mul, map_mul, residue_apply_eq_of_mem_inertiaSubgroupIn P hσ hu hσu, ← map_mul]
  have hone : (⟨π' / π, hu⟩ : P) * ⟨π / π', hu'⟩ = 1 := Subtype.ext (by
    change π' / π * (π / π') = 1
    rw [div_mul_div_comm, mul_comm π' π, div_self (mul_ne_zero hπ hπ')])
  rw [hone, map_one, one_mul]

private theorem mem_of_pow_eq_one {u : AlgebraicClosure ℚ} {m : ℕ} (hm : 0 < m) (hu : u ^ m = 1) : u ∈ P := by
  rcases P.mem_or_inv_mem u with h | h
  · exact h
  · have key : u = (u ^ (m - 1))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ', Nat.sub_add_cancel hm, hu]
    rw [key, ← inv_pow]
    exact pow_mem h _

private theorem tameCharacter_eq_of_div_pow_eq_one (π π' : AlgebraicClosure ℚ) {m : ℕ} (hm : 0 < m)
    (hζ : (π' / π) ^ m = 1) {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) :
    P.tameCharacter π' σ = P.tameCharacter π σ := by
  have hζ0 : π' / π ≠ 0 := by
    intro h
    rw [h, zero_pow hm.ne'] at hζ
    exact zero_ne_one hζ
  have hπ : π ≠ 0 := by
    rintro rfl
    exact hζ0 (div_zero π')
  have hπ' : π' ≠ 0 := by
    rintro rfl
    exact hζ0 (zero_div π)
  have hζinv : (π' / π) ^ (m - 1) = π / π' := by
    rw [← inv_div π' π]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel hm, hζ]
  refine tameCharacter_eq_of_div_mem_of_div_mem P π π' hπ hπ' (mem_of_pow_eq_one P hm hζ) ?_ hσ
  rw [← hζinv]
  exact pow_mem (mem_of_pow_eq_one P hm hζ) _

private theorem tameCharacter_conj_of_isFrobeniusAt (π : AlgebraicClosure ℚ) {m p : ℕ} (hm : 0 < m)
    (hπ : π ^ m = p) {φ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hφ : P.IsFrobeniusAt φ p)
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) :
    P.tameCharacter π (φ * σ * φ⁻¹) = P.tameCharacter π σ ^ p := by
  have hφD : φ ∈ P.decompositionSubgroup ℚ := hφ.mem_decompositionSubgroup

  have hp : (p : AlgebraicClosure ℚ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    rintro rfl
    have h0 := hφ.smul_residue_eq 0
    rw [smul_zero, pow_zero] at h0
    exact zero_ne_one h0
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hπ
    exact hp hπ.symm

  have hπ₁ : (φ⁻¹ π) ^ m = p := by rw [← map_pow, hπ, map_natCast]
  have hπ₁0 : φ⁻¹ π ≠ 0 := (map_ne_zero φ⁻¹).mpr hπ0
  have root_mem : ∀ {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} {ϖ : AlgebraicClosure ℚ},
      ϖ ^ m = p → (τ ϖ / ϖ) ^ m = 1 := by
    intro τ ϖ hϖ
    rw [div_pow, ← map_pow, hϖ, map_natCast, div_self hp]
  have hu : (σ (φ⁻¹ π) / φ⁻¹ π) ^ m = 1 := root_mem hπ₁
  have hu_mem : σ (φ⁻¹ π) / φ⁻¹ π ∈ P := mem_of_pow_eq_one P hm hu
  have hσπ : σ π / π ∈ P := mem_of_pow_eq_one P hm (root_mem hπ)
  have hφu : φ (σ (φ⁻¹ π) / φ⁻¹ π) ∈ P := apply_mem_of_mem_decompositionSubgroup P hφD hu_mem
  have key : (φ * σ * φ⁻¹) π / π = φ (σ (φ⁻¹ π) / φ⁻¹ π) := by
    rw [map_div₀, AlgEquiv.mul_apply, AlgEquiv.mul_apply]
    congr 1
    exact (AlgEquiv.apply_symm_apply φ π).symm
  have hmem : (φ * σ * φ⁻¹) π / π ∈ P := by
    rw [key]
    exact hφu
  rw [tameCharacter_of_mem P π _ hmem]
  have h1 : (⟨(φ * σ * φ⁻¹) π / π, hmem⟩ : P) = ⟨φ (σ (φ⁻¹ π) / φ⁻¹ π), hφu⟩ := Subtype.ext key
  rw [h1]

  have hact : ((⟨φ, hφD⟩ : P.decompositionSubgroup ℚ) • (⟨σ (φ⁻¹ π) / φ⁻¹ π, hu_mem⟩ : P) : P) =
      ⟨φ (σ (φ⁻¹ π) / φ⁻¹ π), hφu⟩ := Subtype.ext rfl
  have h2 : IsLocalRing.residue P ⟨φ (σ (φ⁻¹ π) / φ⁻¹ π), hφu⟩ =
      (⟨φ, hφD⟩ : P.decompositionSubgroup ℚ) • IsLocalRing.residue P ⟨σ (φ⁻¹ π) / φ⁻¹ π, hu_mem⟩ := by
    rw [← hact]
    rfl
  rw [h2, hφ.smul_residue_eq, ← tameCharacter_of_mem P (φ⁻¹ π) σ hu_mem]

  have hζ : (φ⁻¹ π / π) ^ m = 1 := by rw [div_pow, hπ₁, hπ, div_self hp]
  rw [tameCharacter_eq_of_div_pow_eq_one P π (φ⁻¹ π) hm hζ hσ]

end DichTameRows

theorem solution
    (P : ValuationSubring (AlgebraicClosure ℚ)) (π : AlgebraicClosure ℚ) {m p : ℕ} (hm : 0 < m)
    (hπ : π ^ m = p) {φ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hφ : P.IsFrobeniusAt φ p)
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) :
    P.tameCharacter π (φ * σ * φ⁻¹) = P.tameCharacter π σ ^ p :=
  DichTameRows.tameCharacter_conj_of_isFrobeniusAt P π hm hπ hφ hσ

end S_ValuationSubring_tameCharacter_conj_of_isFrobeniusAt
end P2MW
export P2MW.S_ValuationSubring_tameCharacter_conj_of_isFrobeniusAt (solution)
