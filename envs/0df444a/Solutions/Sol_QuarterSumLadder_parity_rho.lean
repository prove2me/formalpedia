-- Prove2me | solution 1 for QuarterSumLadder.parity_rho
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:07:48.869828+00:00
-- url     : https://prove2.me/submissions/5686430e-648c-48df-951f-8e38131cf3f9

module
public import Definitions.Def_QuarterSumLadder_Classes
public import Definitions.Def_QuarterSumLadder_Counts
public import Theorems.Thm_QuarterSumLadder_char_eq_one_iff_pow
public import Theorems.Thm_QuarterSumLadder_neg_one_ne_one_zmod
public import Theorems.Thm_QuarterSumLadder_hp2_of
public import Theorems.Thm_QuarterSumLadder_mod_eight_aux
public import Theorems.Thm_QuarterSumLadder_seventeen_le
public import Theorems.Thm_QuarterSumLadder_two_ne_zero_zmod


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
namespace QuarterSumLadder
theorem _root_.solution (hw : χ 2 = 1) :
    (if (2 : ZMod p) ^ ((p - 1) / 8) = -1 then 1 else 0) % 2 =
      (if 2 ∣ orderOf (2 : ZMod p) then (p - 1) / (4 * orderOf (2 : ZMod p)) else 0) % 2 := by
  have hp2 := hp2_of hp8
  have h1 := neg_one_ne_one_zmod hp2
  have hpq := mod_eight_aux hp8
  have h2Q : (2 : ZMod p) ^ Q p = 1 := (char_eq_one_iff_pow hp8 hχ (two_ne_zero_zmod hp2)).1 hw
  set ρ := orderOf (2 : ZMod p) with hρ
  have hρQ : ρ ∣ Q p := orderOf_dvd_of_pow_eq_one h2Q
  obtain ⟨t, ht⟩ := hρQ
  have hQeven : 2 ∣ Q p := by unfold Q; omega
  have hQ8 : (p - 1) / 8 = Q p / 2 := by unfold Q; omega
  have hdiv : (p - 1) / (4 * ρ) = t := by
    have hρpos : 0 < ρ := orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2
      ⟨Q p, by have := seventeen_le hp8; unfold Q; omega, h2Q⟩)
    rw [hpq, ht, show 4 * (ρ * t) = (4 * ρ) * t by ring, Nat.mul_div_cancel_left _ (by omega)]
  rw [hdiv, hQ8]
  by_cases hρe : 2 ∣ ρ
  · rw [if_pos hρe]
    obtain ⟨σ, hσ⟩ := hρe
    have hρpos : 0 < ρ := orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2
      ⟨Q p, by have := seventeen_le hp8; unfold Q; omega, h2Q⟩)
    have hσpos : 0 < σ := by omega
    have hsq : (2 : ZMod p) ^ σ * (2 : ZMod p) ^ σ = 1 := by
      rw [← pow_add, show σ + σ = ρ by omega, hρ, pow_orderOf_eq_one]
    have hne : (2 : ZMod p) ^ σ ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
    have hσv : (2 : ZMod p) ^ σ = -1 := by
      rcases mul_self_eq_one_iff.1 hsq with h | h
      · exact absurd h hne
      · exact h
    have hQ2 : Q p / 2 = σ * t := by
      rw [ht, hσ, mul_assoc, Nat.mul_div_cancel_left _ two_pos]
    rw [hQ2, pow_mul, hσv]
    rcases Nat.even_or_odd t with he | ho
    · rw [he.neg_one_pow, if_neg h1.symm]; obtain ⟨j, hj⟩ := he; omega
    · rw [ho.neg_one_pow, if_pos rfl]; obtain ⟨j, hj⟩ := ho; omega
  · rw [if_neg hρe]
    have hodd : Nat.Coprime ρ 2 := by
      rw [Nat.coprime_two_right]; exact Nat.odd_iff.2 (by omega)
    have hρh : ρ ∣ Q p / 2 := by
      have : ρ ∣ 2 * (Q p / 2) := by rw [Nat.mul_div_cancel' hQeven]; exact ⟨t, ht⟩
      exact hodd.dvd_of_dvd_mul_left this
    obtain ⟨u, hu⟩ := hρh
    rw [hu, pow_mul, hρ, pow_orderOf_eq_one, one_pow, if_neg h1.symm]
end QuarterSumLadder
