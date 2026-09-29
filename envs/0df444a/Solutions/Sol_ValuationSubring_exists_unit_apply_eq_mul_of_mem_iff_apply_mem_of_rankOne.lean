-- Prove2me | solution 1 for ValuationSubring.exists_unit_apply_eq_mul_of_mem_iff_apply_mem_of_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/70de0c7b-21b1-50fb-8ea1-4f1e6ddf120e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_unit_apply_eq_mul_of_mem_iff_apply_mem_of_rankOne

set_option autoImplicit false

noncomputable section

namespace RankOneIsometry

section Main

open IsLocalRing

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem valuation_apply_le (π : A) (hπ : π ∈ maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (σ : L ≃+* L) (hA : ∀ a : L, a ∈ A ↔ σ a ∈ A) (hσπ : σ (π : L) = (π : L))
    (a : L) (ha : a ≠ 0) : A.valuation (σ a) ≤ A.valuation a := by
  by_contra hlt
  rw [not_le] at hlt
  set v := A.valuation with hv
  have hπL : (π : L) ≠ 0 := fun h => hπ0 (Subtype.ext h)
  have hvπ0 : v (π : L) ≠ 0 := by simpa [hv] using hπL
  have hvπpos : 0 < v (π : L) := zero_lt_iff.mpr hvπ0
  have hvπ1 : v (π : L) < 1 := (A.valuation_lt_one_iff π).mp hπ
  have hσa : σ a ≠ 0 := by simpa using ha
  have hva0 : v a ≠ 0 := by simpa [hv] using ha
  have hvσa0 : v (σ a) ≠ 0 := by simpa [hv] using hσa

  have hy1 : v (a / σ a) < 1 := by
    rw [map_div₀, div_lt_one₀ (zero_lt_iff.mpr hvσa0)]; exact hlt
  have hyA : a / σ a ∈ A := (A.valuation_le_one_iff _).mp hy1.le
  have hym : (⟨a / σ a, hyA⟩ : A) ∈ maximalIdeal A := (A.valuation_lt_one_iff _).mpr hy1

  obtain ⟨N, hN⟩ := hrk (π : L) hπL ⟨a / σ a, hyA⟩ hym
  simp only at hN
  set b : L := a ^ N with hb
  have hb0 : b ≠ 0 := pow_ne_zero _ ha
  have hvb0 : v b ≠ 0 := by simpa [hv] using hb0
  have hvbpos : 0 < v b := zero_lt_iff.mpr hvb0
  have hσb : σ b = (σ a) ^ N := by rw [hb, map_pow]
  have hσb0 : σ b ≠ 0 := by rw [hσb]; exact pow_ne_zero _ hσa
  have hvσb0 : v (σ b) ≠ 0 := by simpa [hv] using hσb0

  have hdag : v b ≤ v (π : L) * v (σ b) := by
    have : v ((a / σ a) ^ N) = v b / v (σ b) := by
      rw [div_pow, map_div₀, hσb, hb, map_pow, map_pow]
    rw [this, div_le_iff₀ (zero_lt_iff.mpr hvσb0)] at hN
    exact hN

  obtain ⟨n₁, hn₁⟩ := hrk b hb0 π hπ
  obtain ⟨n₂, hn₂⟩ := hrk b⁻¹ (inv_ne_zero hb0) π hπ
  rw [map_pow] at hn₁ hn₂

  have Hinh : ∃ p : ℤ, v b ≤ v (π : L) ^ p := by
    refine ⟨-(n₂ : ℤ), ?_⟩
    rw [zpow_neg, zpow_natCast, map_inv₀] at *
    rw [le_inv_comm₀ hvbpos (pow_pos hvπpos _)]
    exact hn₂
  have Hbdd : ∃ B : ℤ, ∀ p : ℤ, v b ≤ v (π : L) ^ p → p ≤ B := by
    refine ⟨n₁, fun p hp => ?_⟩
    by_contra hpn
    rw [not_le] at hpn
    have h1 : v (π : L) ^ p < v (π : L) ^ (n₁ : ℤ) :=
      zpow_lt_zpow_right_of_lt_one₀ hvπpos hvπ1 hpn
    rw [zpow_natCast] at h1
    exact absurd (hp.trans_lt h1) (not_lt.mpr hn₁)
  obtain ⟨p₀, hp₀, hmax⟩ := Int.exists_greatest_of_bdd Hbdd Hinh
  have hnot' : ¬ v b ≤ v (π : L) ^ (p₀ + 1) := fun h => by
    have := hmax _ h; omega
  have hnot : v (π : L) ^ (p₀ + 1) < v b := not_le.mp hnot'

  set c : L := b * (π : L) ^ (-p₀) with hc
  have hvc : v c = v b * (v (π : L) ^ p₀)⁻¹ := by
    rw [hc, map_mul, map_zpow₀, zpow_neg]
  have hcA : c ∈ A := by
    rw [← A.valuation_le_one_iff, ← hv, hvc, mul_inv_le_iff₀ (zpow_pos hvπpos _), one_mul]
    exact hp₀
  have hσc : σ c = σ b * (π : L) ^ (-p₀) := by
    rw [hc, map_mul, map_zpow₀, hσπ]
  have hvσc : v (σ c) = v (σ b) * (v (π : L) ^ p₀)⁻¹ := by
    rw [hσc, map_mul, map_zpow₀, zpow_neg]
  have hσcA : σ c ∉ A := by
    rw [← A.valuation_le_one_iff, ← hv, hvσc, mul_inv_le_iff₀ (zpow_pos hvπpos _), one_mul, not_le]

    have h2 : v (π : L) ^ (p₀ + 1) < v (π : L) * v (σ b) := hnot.trans_le hdag
    rw [zpow_add_one₀ hvπ0, mul_comm] at h2
    exact lt_of_mul_lt_mul_left' h2
  exact hσcA ((hA c).mp hcA)

theorem exists_unit_mul_eq (π : A) (hπ : π ∈ maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (σ : L ≃+* L) (hA : ∀ a : L, a ∈ A ↔ σ a ∈ A) (hσπ : σ (π : L) = (π : L)) :
    ∀ a : L, a ≠ 0 → ∃ u : Aˣ, σ a = u * a := by
  intro a ha
  have hσa : σ a ≠ 0 := by simpa using ha
  have h1 := valuation_apply_le A π hπ hπ0 hrk σ hA hσπ a ha

  have hA' : ∀ x : L, x ∈ A ↔ σ.symm x ∈ A := fun x => by
    conv_lhs => rw [← σ.apply_symm_apply x]
    exact (hA (σ.symm x)).symm
  have hσπ' : σ.symm (π : L) = (π : L) := by
    conv_lhs => rw [← hσπ]
    exact σ.symm_apply_apply _
  have h2 := valuation_apply_le A π hπ hπ0 hrk σ.symm hA' hσπ' (σ a) hσa
  rw [σ.symm_apply_apply] at h2
  have heq : A.valuation (σ a) = A.valuation a := le_antisymm h1 h2

  have hva0 : A.valuation a ≠ 0 := by simpa using ha
  have hu1 : A.valuation (σ a / a) = 1 := by
    rw [map_div₀, heq, div_self hva0]
  have huA : σ a / a ∈ A := (A.valuation_le_one_iff _).mp hu1.le
  have hunit : IsUnit (⟨σ a / a, huA⟩ : A) := (A.valuation_eq_one_iff _).mpr hu1
  refine ⟨hunit.unit, ?_⟩
  rw [IsUnit.unit_spec]
  show σ a = σ a / a * a
  rw [div_mul_cancel₀ _ ha]

end Main

end RankOneIsometry

theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (σ : L ≃+* L) (hA : ∀ a : L, a ∈ A ↔ σ a ∈ A) (hσπ : σ (π : L) = (π : L)) :
    ∀ a : L, a ≠ 0 → ∃ u : Aˣ, σ a = u * a :=
  RankOneIsometry.exists_unit_mul_eq A π hπ hπ0 hrk σ hA hσπ

end

end S_ValuationSubring_exists_unit_apply_eq_mul_of_mem_iff_apply_mem_of_rankOne
end P2MW
export P2MW.S_ValuationSubring_exists_unit_apply_eq_mul_of_mem_iff_apply_mem_of_rankOne (solution)
