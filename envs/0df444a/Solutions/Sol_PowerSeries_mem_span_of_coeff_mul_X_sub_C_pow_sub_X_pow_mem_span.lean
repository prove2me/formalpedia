-- Prove2me | solution 1 for PowerSeries.mem_span_of_coeff_mul_X_sub_C_pow_sub_X_pow_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/ed416939-bfbf-5b3b-afa1-98400bd6852d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PowerSeries_mem_span_of_coeff_mul_X_sub_C_pow_sub_X_pow_mem_span

set_option autoImplicit false
open PowerSeries

namespace FltWs24
namespace A3

variable {A : Type*} [CommRing A]

theorem exists_X_sub_C_pow_eq (a : A) (n : ℕ) (hn : 1 ≤ n) :
    ∃ G : PowerSeries A, ((X : PowerSeries A) - C a) ^ n
      = X ^ n - C ((n : A) * a) * X ^ (n - 1) + C (a ^ 2) * G := by
  induction n, hn using Nat.le_induction with
  | base => exact ⟨0, by simp⟩
  | succ m hm ih =>
    obtain ⟨G, hG⟩ := ih
    refine ⟨X * G + C (m : A) * X ^ (m - 1) - C a * G, ?_⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [pow_succ]
    simp only [Nat.add_sub_cancel_left, Nat.cast_add, Nat.cast_one, map_mul, map_add, map_one,
      Nat.add_succ_sub_one, map_pow] at hG ⊢
    rw [hG]
    ring

theorem coeff_pred_eq (u : PowerSeries A) (a : A) (n : ℕ) (hn : 1 ≤ n) :
    ∃ c : A, coeff (n - 1) (u * ((X : PowerSeries A) - C a) ^ n - X ^ n)
      = a * (-(n : A) * constantCoeff u + a * c) := by
  obtain ⟨G, hG⟩ := exists_X_sub_C_pow_eq a n hn
  refine ⟨coeff (n - 1) (u * G), ?_⟩
  rw [hG, map_sub, mul_add, mul_sub, map_add, map_sub]
  have h1 : coeff (n - 1) (u * X ^ n) = 0 := by
    rw [coeff_mul_X_pow', if_neg (by omega)]
  have h2 : coeff (n - 1) (u * (C ((n : A) * a) * X ^ (n - 1))) = (n : A) * a * constantCoeff u := by
    rw [← mul_assoc, coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self, mul_comm u, coeff_C_mul,
      coeff_zero_eq_constantCoeff]
  have h3 : coeff (n - 1) (u * (C (a ^ 2) * G)) = a ^ 2 * coeff (n - 1) (u * G) := by
    rw [mul_left_comm, coeff_C_mul]
  have h4 : coeff (n - 1) ((X : PowerSeries A) ^ n) = 0 := by
    rw [coeff_X_pow, if_neg (by omega)]
  rw [h1, h2, h3, h4]
  ring

theorem mem_of_coeff_pred_mem [IsLocalRing A] (u : PowerSeries A) (hu : IsUnit (constantCoeff u))
    {a : A} (ha : a ∈ IsLocalRing.maximalIdeal A) {n : ℕ} (hn : 1 ≤ n) (hnu : IsUnit (n : A))
    (I : Ideal A) (h : coeff (n - 1) (u * ((X : PowerSeries A) - C a) ^ n - X ^ n) ∈ I) : a ∈ I := by
  obtain ⟨c, hc⟩ := coeff_pred_eq u a n hn
  rw [hc] at h

  have hunit : IsUnit (-(n : A) * constantCoeff u + a * c) := by
    have h1 : IsUnit (-(n : A) * constantCoeff u) := (hnu.neg).mul hu
    have h2 : a * c ∈ IsLocalRing.maximalIdeal A := Ideal.mul_mem_right _ _ ha
    by_contra hnot
    have h3 : -(n : A) * constantCoeff u + a * c ∈ IsLocalRing.maximalIdeal A :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnot
    have h4 : -(n : A) * constantCoeff u ∈ IsLocalRing.maximalIdeal A := by
      have := Ideal.sub_mem _ h3 h2
      rwa [add_sub_cancel_right] at this
    exact (IsLocalRing.mem_maximalIdeal _).mp h4 h1
  obtain ⟨w, hw⟩ := hunit
  have : a = a * (-(n : A) * constantCoeff u + a * c) * ↑w⁻¹ := by
    rw [← hw, mul_assoc, Units.mul_inv, mul_one]
  rw [this]
  exact I.mul_mem_right _ h

theorem exists_coeff_low_eq {A : Type*} [CommRing A] (u : PowerSeries A) (a : A) (n : ℕ) (hn : 1 ≤ n)
    (k : ℕ) (hk : k + 2 ≤ n) :
    ∃ d : A, coeff k (u * ((X : PowerSeries A) - C a) ^ n - X ^ n) = a ^ 2 * d := by
  obtain ⟨G, hG⟩ := exists_X_sub_C_pow_eq a n hn
  refine ⟨coeff k (u * G), ?_⟩
  rw [hG, map_sub, mul_add, mul_sub, map_add, map_sub]
  have h1 : coeff k (u * X ^ n) = 0 := by
    rw [coeff_mul_X_pow', if_neg (by omega)]
  have h2 : coeff k (u * (C ((n : A) * a) * X ^ (n - 1))) = 0 := by
    rw [← mul_assoc, coeff_mul_X_pow', if_neg (by omega)]
  have h3 : coeff k (u * (C (a ^ 2) * G)) = a ^ 2 * coeff k (u * G) := by
    rw [mul_left_comm, coeff_C_mul]
  have h4 : coeff k ((X : PowerSeries A) ^ n) = 0 := by
    rw [coeff_X_pow, if_neg (by omega)]
  rw [h1, h2, h3, h4]
  ring

end FltWs24.A3

theorem solution
    {A : Type*} [CommRing A] [IsLocalRing A] (n : ℕ) (hn : IsUnit (n : A))
    (u : PowerSeries A) (hu : IsUnit (constantCoeff u))
    (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A) (π : A)
    (h : ∀ k < n, coeff k (u * (X - C a) ^ n - X ^ n) ∈ Ideal.span {π}) :
    a ∈ Ideal.span {π} ∧
      ∀ k, k + 2 ≤ n → coeff k (u * (X - C a) ^ n - X ^ n) ∈ Ideal.span {π * a} := by

  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exfalso; rw [h0, Nat.cast_zero] at hn; exact not_isUnit_zero hn
    · exact hpos
  have ha_mem : a ∈ Ideal.span {π} :=
    FltWs24.A3.mem_of_coeff_pred_mem u hu ha hn1 hn (Ideal.span {π}) (h (n - 1) (by omega))
  refine ⟨ha_mem, fun k hk => ?_⟩
  obtain ⟨d, hd⟩ := FltWs24.A3.exists_coeff_low_eq u a n hn1 k hk
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp ha_mem
  rw [hd, Ideal.mem_span_singleton']
  exact ⟨b * d, by rw [← hb]; ring⟩

end S_PowerSeries_mem_span_of_coeff_mul_X_sub_C_pow_sub_X_pow_mem_span
end P2MW
export P2MW.S_PowerSeries_mem_span_of_coeff_mul_X_sub_C_pow_sub_X_pow_mem_span (solution)
