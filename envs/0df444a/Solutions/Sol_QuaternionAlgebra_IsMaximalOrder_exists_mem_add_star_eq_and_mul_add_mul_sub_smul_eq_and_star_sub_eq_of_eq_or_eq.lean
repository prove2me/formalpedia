-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_mem_add_star_eq_and_mul_add_mul_sub_smul_eq_and_star_sub_eq_of_eq_or_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c37fa71e-f0a0-5718-8abb-b303a12b90a8

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_involutive_of_mul_self_eq_neg_smul_of_forall_mul_eq_star_mul
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_symm
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_mem_trd_eq_nrd_eq_forall_sq_sub_mul_add_ne_zero_of_isIndefiniteRamifiedExactlyAt
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_trd_mul_mem_and_exists_trd_mul_eq_of_isIndefiniteRamifiedExactlyAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_mem_add_star_eq_and_mul_add_mul_sub_smul_eq_and_star_sub_eq_of_eq_or_eq
p2m_attr_erase "instance" "CerednikDrinfeld.CosetGraph.projGraphAction CerednikDrinfeld.CosetGraph.projVertMulAction CerednikDrinfeld.CosetGraph.awayVertMulAction CerednikDrinfeld.CosetGraph.actionKer_normal CerednikDrinfeld.CosetGraph.vertMulAction CerednikDrinfeld.Mumford.dartAction"
p2m_attr_erase "simp" "QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

namespace RamStruct

variable {a b : ℚ}

theorem smul_one_eq_coe (c : ℚ) : c • (1 : ℍ[ℚ, a, b]) = ((c : ℚ) : ℍ[ℚ, a, b]) := by
  rw [← QuaternionAlgebra.coe_mul_eq_smul, mul_one]

theorem disc_ne_zero {p : ℕ} [Fact p.Prime] (t n : ZMod p) (h : ∀ x : ZMod p, x ^ 2 - t * x + n ≠ 0) :
    t ^ 2 - 4 * n ≠ 0 := by
  intro hd
  by_cases h2 : (2 : ZMod p) = 0
  · have hp2 : p = 2 := by
      have h2' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
      have : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h2'
      exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this
    subst hp2
    clear h2
    revert t n h hd
    decide +revert
  · apply h (t * 2⁻¹)
    have h22 : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
    linear_combination ((2 : ZMod p)⁻¹ ^ 2 - 2⁻¹) * hd + (n * (2 * 2⁻¹ - 1)) * h22

theorem star_eq_neg_of_mul_self {c : ℚ} (hc : 0 < c) (μ : ℍ[ℚ, a, b])
    (hμ : μ * μ = -(c • (1 : ℍ[ℚ, a, b]))) : star μ = -μ := by
  have htr := add_star_eq_coe_trd μ
  have hnr := mul_star_eq_coe_nrd μ
  have hs : star μ = ((trd μ : ℚ) : ℍ[ℚ, a, b]) - μ := by rw [← htr]; abel

  have h1 : μ * star μ = (trd μ) • μ - μ * μ := by rw [hs, mul_sub, QuaternionAlgebra.mul_coe_eq_smul]
  rw [hnr, hμ, sub_neg_eq_add] at h1
  have key : (trd μ) • μ = ((nrd μ : ℚ) : ℍ[ℚ, a, b]) - c • 1 := eq_sub_of_add_eq h1.symm
  by_cases h0 : trd μ = 0
  · rw [hs, h0]; simp
  · exfalso
    have hI : μ.imI = 0 := by
      have := congrArg QuaternionAlgebra.imI key
      simp [h0] at this; exact this
    have hJ : μ.imJ = 0 := by
      have := congrArg QuaternionAlgebra.imJ key
      simp [h0] at this; exact this
    have hK : μ.imK = 0 := by
      have := congrArg QuaternionAlgebra.imK key
      simp [h0] at this; exact this
    have hre := congrArg QuaternionAlgebra.re hμ
    simp [hI, hJ, hK] at hre
    nlinarith [sq_nonneg μ.re]

theorem core {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hpr : r ≠ p)
    (hB : IsIndefiniteRamifiedExactlyAt a b p r)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((p * r : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ) :
    ∃ (ω : ℍ[ℚ, a, b]) (hω : ω ∈ Λ) (t n : ℤ),

      ω + Star.star ω = ((t : ℚ) : ℍ[ℚ, a, b]) ∧
      ω * Star.star ω = ((n : ℚ) : ℍ[ℚ, a, b]) ∧
      (∀ x : ZMod p, x ^ 2 - (t : ZMod p) * x + (n : ZMod p) ≠ 0) ∧
      ((t : ZMod p) ^ 2 - 4 * (n : ZMod p) ≠ 0) ∧

      (∃ z : ℍ[ℚ, a, b], z ∈ Λ ∧
        (μ : ℍ[ℚ, a, b]) * ω + ω * μ - (t : ℚ) • (μ : ℍ[ℚ, a, b]) = (p : ℚ) • z) ∧

      (∃ (c₀ c₁ : ℤ) (y : ℍ[ℚ, a, b]), y ∈ Λ ∧
        (star ⟨ω, hω⟩ : ℍ[ℚ, a, b]) - ω =
          (μ : ℍ[ℚ, a, b]) * (((c₀ : ℚ) : ℍ[ℚ, a, b]) + (c₁ : ℚ) • ω) + (p : ℚ) • y) ∧

      (∃ (l₁ l₂ : ℍ[ℚ, a, b]), l₁ ∈ Λ ∧ l₂ ∈ Λ ∧
        (star ⟨ω, hω⟩ : ℍ[ℚ, a, b]) = ω + (p : ℚ) • l₁ + (μ : ℍ[ℚ, a, b]) * l₂) ∧

      (star μ : ℍ[ℚ, a, b]) = -(μ : ℍ[ℚ, a, b]) ∧
      (∀ x : ↥Λ, star (star x) = x) ∧
      (∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, star ⟨1, h1⟩ = ⟨1, h1⟩) := by
  classical
  have hone : (1 : ℍ[ℚ, a, b]) ∈ Λ := hΛ.isOrder.one_mem

  obtain ⟨ω, hω, t, n, htrd, hnrd, hroot⟩ :=
    IsMaximalOrder.exists_mem_trd_eq_nrd_eq_forall_sq_sub_mul_add_ne_zero_of_isIndefiniteRamifiedExactlyAt hB Λ hΛ p (Or.inl rfl)
  have ha1 : ω + Star.star ω = ((t : ℚ) : ℍ[ℚ, a, b]) := by rw [add_star_eq_coe_trd, htrd]
  have ha2 : ω * Star.star ω = ((n : ℚ) : ℍ[ℚ, a, b]) := by rw [mul_star_eq_coe_nrd, hnrd]
  have hωbar : Star.star ω = ((t : ℚ) : ℍ[ℚ, a, b]) - ω := by rw [← ha1]; abel
  have hdisc := disc_ne_zero (t : ZMod p) (n : ZMod p) hroot

  have hc : (0 : ℚ) < ((p * r : ℕ) : ℚ) := by exact_mod_cast Nat.mul_pos (Fact.out : p.Prime).pos (Fact.out : r.Prime).pos
  have hμbar : Star.star (μ : ℍ[ℚ, a, b]) = -(μ : ℍ[ℚ, a, b]) := star_eq_neg_of_mul_self hc _ hμ
  have hμ0 : (μ : ℍ[ℚ, a, b]) ≠ 0 := by
    intro h; rw [h, zero_mul] at hμ
    have := congrArg QuaternionAlgebra.re hμ
    simp at this
    rcases this with h' | h'
    · exact (Fact.out : p.Prime).ne_zero h'
    · exact (Fact.out : r.Prime).ne_zero h'
  have hμu : IsUnit (μ : ℍ[ℚ, a, b]) := hB.isUnit_of_ne_zero _ hμ0

  have he : (star μ : ℍ[ℚ, a, b]) = -(μ : ℍ[ℚ, a, b]) := by
    apply hμu.mul_left_cancel
    rw [hstar μ, hμbar, neg_mul, mul_neg]

  have hh : ∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, star ⟨1, h1⟩ = ⟨1, h1⟩ := by
    intro h1
    apply Subtype.ext
    apply hμu.mul_left_cancel
    have := hstar ⟨1, h1⟩
    rw [this, star_one, one_mul, mul_one]

  have hf : ∀ x : ↥Λ, star (star x) = x :=
    QuaternionAlgebra.involutive_of_mul_self_eq_neg_smul_of_forall_mul_eq_star_mul hc (μ : ℍ[ℚ, a, b])
      (by rw [hμ, neg_smul]) Subtype.val Subtype.val_injective star hstar

  obtain ⟨s, hs⟩ := (IsMaximalOrder.trd_mul_mem_and_exists_trd_mul_eq_of_isIndefiniteRamifiedExactlyAt hpr hB Λ hΛ μ hμ).1 ω hω
  have hX : (μ : ℍ[ℚ, a, b]) * ω + ω * μ - (t : ℚ) • (μ : ℍ[ℚ, a, b]) = ((((p * r : ℕ) : ℚ) * s : ℚ) : ℍ[ℚ, a, b]) := by
    have h1 := add_star_eq_coe_trd ((μ : ℍ[ℚ, a, b]) * ω)
    rw [hs, star_mul, hμbar, hωbar, sub_mul, mul_neg, mul_neg, QuaternionAlgebra.coe_mul_eq_smul] at h1
    rw [← h1]
    abel
  have hz : (((r : ℕ) : ℤ) * s : ℤ) • (1 : ℍ[ℚ, a, b]) ∈ Λ := Λ.smul_mem _ hone
  have hzeq : (p : ℚ) • ((((r : ℕ) : ℤ) * s : ℤ) • (1 : ℍ[ℚ, a, b])) = ((((p * r : ℕ) : ℚ) * s : ℚ) : ℍ[ℚ, a, b]) := by
    rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_one_eq_coe]
    congr 1
    push_cast
    ring
  have hb : (μ : ℍ[ℚ, a, b]) * ω + ω * μ - (t : ℚ) • (μ : ℍ[ℚ, a, b]) = (p : ℚ) • ((((r : ℕ) : ℤ) * s : ℤ) • (1 : ℍ[ℚ, a, b])) := by
    rw [hzeq, hX]

  have hδ : (star ⟨ω, hω⟩ : ℍ[ℚ, a, b]) - ω = (μ : ℍ[ℚ, a, b]) * (((s : ℚ) : ℍ[ℚ, a, b]) + ((0 : ℤ) : ℚ) • ω) + (p : ℚ) • (0 : ℍ[ℚ, a, b]) := by
    have hL : (μ : ℍ[ℚ, a, b]) * ((star ⟨ω, hω⟩ : ℍ[ℚ, a, b]) - ω) = -((((p * r : ℕ) : ℚ) * s : ℚ) : ℍ[ℚ, a, b]) := by
      have h2 := hstar ⟨ω, hω⟩
      rw [mul_sub, h2, hωbar, sub_mul, QuaternionAlgebra.coe_mul_eq_smul, ← hX]
      abel
    have hR : (μ : ℍ[ℚ, a, b]) * ((μ : ℍ[ℚ, a, b]) * ((s : ℚ) : ℍ[ℚ, a, b])) = -((((p * r : ℕ) : ℚ) * s : ℚ) : ℍ[ℚ, a, b]) := by
      rw [← mul_assoc, hμ, neg_mul, smul_mul_assoc, one_mul, ← QuaternionAlgebra.coe_mul_eq_smul, ← QuaternionAlgebra.coe_mul]
    have := hμu.mul_left_cancel (hL.trans hR.symm)
    rw [this]; simp
  refine ⟨ω, hω, t, n, ha1, ha2, hroot, hdisc, ⟨_, hz, hb⟩, ⟨s, 0, 0, Λ.zero_mem, hδ⟩, ?_, he, hf, hh⟩

  refine ⟨0, ((s : ℚ) : ℍ[ℚ, a, b]), Λ.zero_mem, ?_, ?_⟩
  · have : ((s : ℚ) : ℍ[ℚ, a, b]) = (s : ℤ) • (1 : ℍ[ℚ, a, b]) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, ← QuaternionAlgebra.coe_mul_eq_smul, mul_one]
    rw [this]; exact Λ.smul_mem _ hone
  · rw [sub_eq_iff_eq_add] at hδ
    rw [hδ]
    simp only [Int.cast_zero, zero_smul, add_zero, smul_zero]
    abel

end RamStruct

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    {p : ℕ} [Fact p.Prime] (hp : p = q ∨ p = q') :
    ∃ (ω : ℍ[ℚ, a, b]) (hω : ω ∈ Λ) (t n : ℤ),

      ω + Star.star ω = ((t : ℚ) : ℍ[ℚ, a, b]) ∧
      ω * Star.star ω = ((n : ℚ) : ℍ[ℚ, a, b]) ∧
      (∀ x : ZMod p, x ^ 2 - (t : ZMod p) * x + (n : ZMod p) ≠ 0) ∧
      ((t : ZMod p) ^ 2 - 4 * (n : ZMod p) ≠ 0) ∧

      (∃ z : ℍ[ℚ, a, b], z ∈ Λ ∧
        (μ : ℍ[ℚ, a, b]) * ω + ω * μ - (t : ℚ) • (μ : ℍ[ℚ, a, b]) = (p : ℚ) • z) ∧

      (∃ (c₀ c₁ : ℤ) (y : ℍ[ℚ, a, b]), y ∈ Λ ∧
        (star ⟨ω, hω⟩ : ℍ[ℚ, a, b]) - ω =
          (μ : ℍ[ℚ, a, b]) * (((c₀ : ℚ) : ℍ[ℚ, a, b]) + (c₁ : ℚ) • ω) + (p : ℚ) • y) ∧

      (∃ (l₁ l₂ : ℍ[ℚ, a, b]), l₁ ∈ Λ ∧ l₂ ∈ Λ ∧
        (star ⟨ω, hω⟩ : ℍ[ℚ, a, b]) = ω + (p : ℚ) • l₁ + (μ : ℍ[ℚ, a, b]) * l₂) ∧

      (star μ : ℍ[ℚ, a, b]) = -(μ : ℍ[ℚ, a, b]) ∧
      (∀ x : ↥Λ, star (star x) = x) ∧
      (∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, star ⟨1, h1⟩ = ⟨1, h1⟩) := by
  rcases hp with rfl | rfl
  · exact RamStruct.core hqq' hB Λ hΛ μ hμ star hstar
  · exact RamStruct.core (Ne.symm hqq') hB.symm Λ hΛ μ (by rwa [Nat.mul_comm] at hμ) star hstar

end S_QuaternionAlgebra_IsMaximalOrder_exists_mem_add_star_eq_and_mul_add_mul_sub_smul_eq_and_star_sub_eq_of_eq_or_eq
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_mem_add_star_eq_and_mul_add_mul_sub_smul_eq_and_star_sub_eq_of_eq_or_eq (solution)
