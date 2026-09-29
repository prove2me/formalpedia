-- Prove2me | solution 1 for ValuationSubring.exists_valuation_pow_eq_valuation_zpow_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/128b5d7e-d468-5f98-8b4e-7ae0e77bc66d

import Mathlib
import Theorems.Thm_ValuationSubring_exists_pow_valuation_eq_valuation_algebraMap_of_isAlgebraic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_valuation_pow_eq_valuation_zpow_of_isAlgebraic

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Valuation
p2m_export "Valuation" "ne_zero_iff map_neg integer comap"
namespace RatComm
p2m_open "Valuation"

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (w : Valuation ℚ Γ₀)

theorem map_natCast_le_one (n : ℕ) : w n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    exact (w.map_add _ _).trans (max_le ih (by rw [w.map_one]))

theorem map_intCast_le_one (a : ℤ) : w a ≤ 1 := by
  obtain ⟨n, rfl | rfl⟩ := a.eq_nat_or_neg
  · exact_mod_cast map_natCast_le_one w n
  · rw [Int.cast_neg, Valuation.map_neg]; exact_mod_cast map_natCast_le_one w n

theorem exists_prime_dvd_map_lt_one {n : ℕ} (hn0 : n ≠ 0) (hn : w n < 1) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ w p < 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hn1 : n ≠ 1 := by rintro rfl; simp at hn
    obtain ⟨p, hp, m, rfl⟩ := Nat.exists_prime_and_dvd hn1
    by_cases hwp : w p < 1
    · exact ⟨p, hp, dvd_mul_right p m, hwp⟩
    · have hp1 : w p = 1 := le_antisymm (map_natCast_le_one w p) (not_lt.mp hwp)
      have hm : w m < 1 := by
        have : w ((p * m : ℕ) : ℚ) = w p * w m := by push_cast; exact w.map_mul _ _
        rwa [this, hp1, one_mul] at hn
      have hm0 : m ≠ 0 := by rintro rfl; exact hn0 (mul_zero p)
      have hmlt : m < p * m := lt_mul_left (Nat.pos_of_ne_zero hm0) hp.one_lt
      obtain ⟨ℓ, hℓ, hℓm, hwℓ⟩ := ih m hmlt hm0 hm
      exact ⟨ℓ, hℓ, dvd_mul_of_dvd_right hℓm p, hwℓ⟩

theorem map_prime_eq_one_of_ne {ℓ p : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hwℓ : w ℓ < 1) (hne : p ≠ ℓ) :
    w p = 1 := by
  by_contra hwp
  have hwp' : w p < 1 := lt_of_le_of_ne (map_natCast_le_one w p) hwp
  have hcop : IsCoprime (p : ℤ) (ℓ : ℤ) := Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hℓ).mpr hne)
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : w ((a * p + b * ℓ : ℤ) : ℚ) = 1 := by rw [hab]; simp
  push_cast at h1
  have hlt : w ((a : ℚ) * p + b * ℓ) < 1 := by
    refine lt_of_le_of_lt (w.map_add _ _) (max_lt ?_ ?_)
    · rw [w.map_mul]
      exact lt_of_le_of_lt (mul_le_mul_left (map_intCast_le_one w a) _) (by rwa [one_mul])
    · rw [w.map_mul]
      exact lt_of_le_of_lt (mul_le_mul_left (map_intCast_le_one w b) _) (by rwa [one_mul])
  exact (lt_irrefl _) (h1 ▸ hlt)

theorem map_natCast_eq_one_of_not_dvd {ℓ : ℕ} (hℓ : ℓ.Prime) (hwℓ : w ℓ < 1) {m : ℕ} (hm0 : m ≠ 0)
    (hnd : ¬ ℓ ∣ m) : w m = 1 := by
  by_contra h
  obtain ⟨p, hp, hpm, hwp⟩ := exists_prime_dvd_map_lt_one w hm0 (lt_of_le_of_ne (map_natCast_le_one w m) h)
  have hpl : p = ℓ := by
    by_contra hne; exact (lt_irrefl _) ((map_prime_eq_one_of_ne w hℓ hp hwℓ hne) ▸ hwp)
  exact hnd (hpl ▸ hpm)

theorem exists_map_natCast_eq_pow {ℓ : ℕ} (hℓ : ℓ.Prime) (hwℓ : w ℓ < 1) {n : ℕ} (hn0 : n ≠ 0) :
    ∃ e : ℕ, w n = w ℓ ^ e := by
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 ℓ hℓ.ne_one
  refine ⟨e, ?_⟩
  have hm0 : m ≠ 0 := by rintro rfl; exact hn0 (mul_zero _)
  push_cast
  rw [w.map_mul, w.map_pow, map_natCast_eq_one_of_not_dvd w hℓ hwℓ hm0 hm, mul_one]

theorem exists_map_eq_zpow {ℓ : ℕ} (hℓ : ℓ.Prime) (hwℓ : w ℓ < 1) {c : ℚ} (hc : c ≠ 0) :
    ∃ k : ℤ, w c = w ℓ ^ k := by
  have hℓ0 : w ℓ ≠ 0 := by rw [Valuation.ne_zero_iff]; exact_mod_cast hℓ.ne_zero
  have hnum : c.num ≠ 0 := Rat.num_ne_zero.mpr hc
  obtain ⟨e₁, he₁⟩ := exists_map_natCast_eq_pow w hℓ hwℓ (Int.natAbs_ne_zero.mpr hnum)
  obtain ⟨e₂, he₂⟩ := exists_map_natCast_eq_pow w hℓ hwℓ c.den_nz
  refine ⟨(e₁ : ℤ) - e₂, ?_⟩
  have hwnum : w (c.num : ℚ) = w ℓ ^ e₁ := by
    rw [← he₁, Nat.cast_natAbs, Int.cast_abs]
    rcases abs_choice ((c.num : ℤ) : ℚ) with h | h
    · rw [h]
    · rw [h, Valuation.map_neg]
  conv_lhs => rw [← Rat.num_div_den c]
  rw [map_div₀, hwnum, he₂, zpow_sub₀ hℓ0, zpow_natCast, zpow_natCast]

theorem exists_prime_map_lt_one {c : ℚ} (hc : c ≠ 0) (h : w c < 1) : ∃ ℓ : ℕ, ℓ.Prime ∧ w ℓ < 1 := by
  have hnum : c.num ≠ 0 := Rat.num_ne_zero.mpr hc
  have hden : w (c.den : ℚ) ≤ 1 := map_natCast_le_one w c.den
  have hden0 : w (c.den : ℚ) ≠ 0 := by rw [Valuation.ne_zero_iff]; exact_mod_cast c.den_nz
  have hnumlt : w (c.num : ℚ) < 1 := by
    conv_lhs at h => rw [← Rat.num_div_den c]
    rw [map_div₀, div_lt_one₀ (zero_lt_iff.mpr hden0)] at h
    exact h.trans_le hden
  have habs : w ((c.num.natAbs : ℕ) : ℚ) < 1 := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    rcases abs_choice ((c.num : ℤ) : ℚ) with h' | h'
    · rwa [h']
    · rwa [h', Valuation.map_neg]
  obtain ⟨ℓ, hℓ, -, hwℓ⟩ := exists_prime_dvd_map_lt_one w (Int.natAbs_ne_zero.mpr hnum) habs
  exact ⟨ℓ, hℓ, hwℓ⟩

end Valuation.RatComm

open Valuation.RatComm in

theorem solution
    {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F] (O : ValuationSubring F)
    {π₀ : F} (h0 : O.valuation π₀ ≠ 0) (h1 : O.valuation π₀ < 1) {x : F} (hx : x ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ k : ℤ, O.valuation x ^ m = O.valuation π₀ ^ k := by
  set v := O.valuation with hv
  let w : Valuation ℚ O.ValueGroup := v.comap (algebraMap ℚ F)
  have hw : ∀ c : ℚ, w c = v (algebraMap ℚ F c) := fun c => rfl
  have hπ0 : π₀ ≠ 0 := fun h => h0 (by rw [h, Valuation.map_zero])
  obtain ⟨n₀, hn₀, c₀, hc₀, hπ⟩ := O.exists_pow_valuation_eq_valuation_algebraMap_of_isAlgebraic (E := ℚ) hπ0
  rw [Valuation.map_pow, ← hw] at hπ
  have hwc₀ : w c₀ < 1 := by rw [← hπ]; exact pow_lt_one₀ zero_le' h1 (by omega)
  obtain ⟨ℓ, hℓ, hwℓ⟩ := exists_prime_map_lt_one w hc₀ hwc₀
  have hℓ0 : w ℓ ≠ 0 := by rw [Valuation.ne_zero_iff]; exact_mod_cast hℓ.ne_zero
  obtain ⟨k₀, hk₀⟩ := exists_map_eq_zpow w hℓ hwℓ hc₀

  have hk₀pos : 0 < k₀ := by
    by_contra hle
    push Not at hle
    have : 1 ≤ w ℓ ^ k₀ := one_le_zpow_of_nonpos₀ (zero_lt_iff.mpr hℓ0) hwℓ.le hle
    rw [← hk₀] at this
    exact (lt_irrefl _) (this.trans_lt hwc₀)
  obtain ⟨K₀, hK₀⟩ := Int.eq_ofNat_of_zero_le hk₀pos.le
  have hK₀pos : 0 < K₀ := by omega

  obtain ⟨n₁, hn₁, c₁, hc₁, hx1⟩ := O.exists_pow_valuation_eq_valuation_algebraMap_of_isAlgebraic (E := ℚ) hx
  rw [Valuation.map_pow, ← hw] at hx1
  obtain ⟨k₁, hk₁⟩ := exists_map_eq_zpow w hℓ hwℓ hc₁
  refine ⟨n₁ * K₀, Nat.mul_pos hn₁ hK₀pos, (n₀ : ℤ) * k₁, ?_⟩
  calc v x ^ (n₁ * K₀) = (v x ^ n₁) ^ K₀ := pow_mul _ _ _
    _ = (w ℓ ^ k₁) ^ (K₀ : ℤ) := by rw [hx1, hk₁, zpow_natCast]
    _ = (w ℓ ^ (K₀ : ℤ)) ^ k₁ := by rw [← zpow_mul, ← zpow_mul, mul_comm]
    _ = (v π₀ ^ n₀) ^ k₁ := by rw [← hK₀, ← hk₀, hπ]
    _ = v π₀ ^ ((n₀ : ℤ) * k₁) := by rw [zpow_mul, zpow_natCast]

end S_ValuationSubring_exists_valuation_pow_eq_valuation_zpow_of_isAlgebraic
end P2MW
export P2MW.S_ValuationSubring_exists_valuation_pow_eq_valuation_zpow_of_isAlgebraic (solution)
