-- Prove2me | solution 1 for Padic.exists_eq_one_add_prime_pow_mul_pow_of_dvd_valuation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/78da2ee3-e76d-59a8-b1fe-ad28316a8e69

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Padic_exists_eq_one_add_prime_pow_mul_pow_of_dvd_valuation

set_option autoImplicit false

namespace Padic
p2m_export "Padic" "coe_one norm_p_zpow norm_eq_zpow_neg_valuation valuation coe_mul norm_p coe_add"
namespace U6UnitsModPthPowersAux
p2m_open "Padic"

open Polynomial

theorem prime_pow_three_dvd {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) {j : ℕ} (h2 : 2 ≤ j)
    (hj : j ≤ p) : p ^ 3 ∣ p ^ j * p.choose j := by
  rcases Nat.lt_or_ge j p with hlt | hge
  · have hd : p ∣ p.choose j := hp.dvd_choose_self (by omega) hlt
    calc p ^ 3 ∣ p ^ (j + 1) := pow_dvd_pow p (by omega)
      _ = p ^ j * p := pow_succ p j
      _ ∣ p ^ j * p.choose j := mul_dvd_mul_left _ hd
  · have : j = p := le_antisymm hj hge
    subst this
    rw [Nat.choose_self, mul_one]
    exact pow_dvd_pow _ h3

theorem exists_one_add_prime_mul_pow_prime_eq {R : Type} [CommRing R] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (x : R) :
    ∃ c : R, (1 + (p : R) * x) ^ p = 1 + (p : R) ^ 2 * x + (p : R) ^ 3 * c := by
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hS : (1 + ((q + 1 : ℕ) : R) * x) ^ (q + 1) =
      (∑ k ∈ Finset.range q,
          (((q + 1 : ℕ) : R) * x) ^ (k + 1 + 1) * (((q + 1).choose (k + 1 + 1) : ℕ) : R)) +
        (((q + 1 : ℕ) : R) ^ 2 * x + 1) := by
    rw [add_comm (1 : R), add_pow, Finset.sum_range_succ', Finset.sum_range_succ', add_assoc]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [one_pow, mul_one]
    · simp only [zero_add, pow_one, pow_zero, one_pow, mul_one, Nat.choose_zero_right,
        Nat.choose_one_right, Nat.cast_one]
      ring
  suffices h : ((q + 1 : ℕ) : R) ^ 3 ∣ ∑ k ∈ Finset.range q,
      (((q + 1 : ℕ) : R) * x) ^ (k + 1 + 1) * (((q + 1).choose (k + 1 + 1) : ℕ) : R) by
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by rw [hS, hc]; ring⟩
  apply Finset.dvd_sum
  intro k hk
  rw [Finset.mem_range] at hk
  have key : (((q + 1) ^ 3 : ℕ) : R) ∣ (((q + 1) ^ (k + 1 + 1) * (q + 1).choose (k + 1 + 1) : ℕ) : R) :=
    Nat.cast_dvd_cast (prime_pow_three_dvd hp h3 (j := k + 1 + 1) (by omega) (by omega))
  rw [Nat.cast_pow, Nat.cast_mul, Nat.cast_pow] at key
  have hrw : (((q + 1 : ℕ) : R) * x) ^ (k + 1 + 1) * (((q + 1).choose (k + 1 + 1) : ℕ) : R) =
      ((q + 1 : ℕ) : R) ^ (k + 1 + 1) * (((q + 1).choose (k + 1 + 1) : ℕ) : R) * x ^ (k + 1 + 1) := by
    ring
  rw [hrw]
  exact key.mul_right _

theorem exists_one_add_pow_eq {R : Type} [CommRing R] (y : R) :
    ∀ n : ℕ, ∃ e : R, (1 + y) ^ n = 1 + (n : R) * y + y ^ 2 * e
  | 0 => ⟨0, by simp⟩
  | n + 1 => by
    obtain ⟨e, he⟩ := exists_one_add_pow_eq y n
    exact ⟨(n : R) + e + e * y, by rw [pow_succ, he]; push_cast; ring⟩

variable {p : ℕ} [Fact p.Prime]

theorem norm_mul_padicInt (z₁ z₂ : ℤ_[p]) : ‖z₁ * z₂‖ = ‖z₁‖ * ‖z₂‖ := by
  rw [PadicInt.norm_def, PadicInt.coe_mul, norm_mul, ← PadicInt.norm_def, ← PadicInt.norm_def]

theorem isUnit_one_add_prime_mul (s : ℤ_[p]) : IsUnit (1 + (p : ℤ_[p]) * s) := by
  have h : 1 + (p : ℤ_[p]) * s = 1 - -((p : ℤ_[p]) * s) := by ring
  rw [h]
  apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
  rw [PadicInt.mem_nonunits, norm_neg, norm_mul_padicInt, PadicInt.norm_p]
  calc (p : ℝ)⁻¹ * ‖s‖ ≤ (p : ℝ)⁻¹ * 1 := by gcongr; exact PadicInt.norm_le_one s
    _ < 1 := by
      rw [mul_one]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)

theorem exists_pow_prime_eq_one_add_prime_sq_mul (hp2 : p ≠ 2) (s : ℤ_[p]) :
    ∃ w : ℤ_[p], w ^ p = 1 + (p : ℤ_[p]) ^ 2 * s := by
  have hp : p.Prime := Fact.out
  obtain ⟨c, hc⟩ := exists_one_add_prime_mul_pow_prime_eq (R := ℤ_[p]) hp hp2 s
  set b : ℤ_[p] := 1 + (p : ℤ_[p]) ^ 2 * s with hb
  set a₀ : ℤ_[p] := 1 + (p : ℤ_[p]) * s with ha₀
  set F : Polynomial ℤ_[p] := X ^ p - C b with hFdef
  have hF : ∀ z : ℤ_[p], aeval z F = z ^ p - b := by
    intro z; simp [hFdef]
  have hF' : ∀ z : ℤ_[p], aeval z (derivative F) = (p : ℤ_[p]) * z ^ (p - 1) := by
    intro z; simp [hFdef, derivative_X_pow]
  have hp_inv_pos : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.pos)
  have hp_inv_lt : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hnF' : ‖aeval a₀ (derivative F)‖ = (p : ℝ)⁻¹ := by
    rw [hF', norm_mul_padicInt, PadicInt.norm_p,
      PadicInt.isUnit_iff.mp ((isUnit_one_add_prime_mul s).pow (p - 1)), mul_one]
  have hnF : ‖aeval a₀ F‖ ≤ (p : ℝ)⁻¹ ^ 3 := by
    rw [hF]
    have : a₀ ^ p - b = (p : ℤ_[p]) ^ 3 * c := by rw [ha₀, hb, hc]; ring
    rw [this, norm_mul_padicInt]
    calc ‖(p : ℤ_[p]) ^ 3‖ * ‖c‖ ≤ ‖(p : ℤ_[p])‖ ^ 3 * 1 := by
          gcongr
          · exact norm_pow_le _ _
          · exact PadicInt.norm_le_one c
      _ = (p : ℝ)⁻¹ ^ 3 := by rw [mul_one, PadicInt.norm_p]
  have hnorm : ‖aeval a₀ F‖ < ‖aeval a₀ (derivative F)‖ ^ 2 := by
    rw [hnF']
    calc ‖aeval a₀ F‖ ≤ (p : ℝ)⁻¹ ^ 3 := hnF
      _ = (p : ℝ)⁻¹ ^ 2 * (p : ℝ)⁻¹ := pow_succ _ _
      _ < (p : ℝ)⁻¹ ^ 2 * 1 := mul_lt_mul_of_pos_left hp_inv_lt (pow_pos hp_inv_pos 2)
      _ = (p : ℝ)⁻¹ ^ 2 := mul_one _
  obtain ⟨w, hw, -, -, -⟩ := hensels_lemma hnorm
  exact ⟨w, sub_eq_zero.mp (by rw [← hF]; exact hw)⟩

theorem exists_eq_pow_prime_mul_one_add (u : ℤ_[p]) (hu : IsUnit u) :
    ∃ t : ℤ_[p], u = u ^ p * (1 + (p : ℤ_[p]) * t) := by
  have hmem : u - u ^ p ∈ Ideal.span {(p : ℤ_[p])} := by
    rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow,
      ZMod.pow_card, sub_self]
  obtain ⟨t₀, ht₀⟩ := Ideal.mem_span_singleton'.mp hmem
  have hUp : ((hu.unit ^ p : ℤ_[p]ˣ) : ℤ_[p]) = u ^ p := by
    rw [Units.val_pow_eq_pow_val, hu.unit_spec]
  have h1 : u ^ p * ((hu.unit ^ p)⁻¹ : ℤ_[p]ˣ) = 1 := by
    rw [← hUp, Units.mul_inv]
  refine ⟨t₀ * ((hu.unit ^ p)⁻¹ : ℤ_[p]ˣ), ?_⟩
  linear_combination (-((p : ℤ_[p]) * t₀)) * h1 - ht₀

theorem exists_one_add_prime_mul_eq (t : ℤ_[p]) :
    ∃ (c : ℕ) (s : ℤ_[p]), 1 + (p : ℤ_[p]) * t = (1 + (p : ℤ_[p])) ^ c * (1 + (p : ℤ_[p]) ^ 2 * s) := by
  obtain ⟨t₂, ht₂⟩ : ∃ t₂ : ℤ_[p], t₂ * p = t - ((PadicInt.toZMod t).val : ℤ_[p]) := by
    apply Ideal.mem_span_singleton'.mp
    rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub,
      map_natCast, ZMod.natCast_zmod_val, sub_self]
  obtain ⟨e, he⟩ := exists_one_add_pow_eq (p : ℤ_[p]) (PadicInt.toZMod t).val
  have hg : IsUnit ((1 + (p : ℤ_[p])) ^ (PadicInt.toZMod t).val) := by
    have := (isUnit_one_add_prime_mul (1 : ℤ_[p])).pow (PadicInt.toZMod t).val
    rwa [mul_one] at this
  have h1 := hg.mul_val_inv
  refine ⟨(PadicInt.toZMod t).val, (t₂ - e) * (hg.unit⁻¹ : ℤ_[p]ˣ), ?_⟩
  linear_combination (-((p : ℤ_[p]) ^ 2 * (t₂ - e))) * h1 - he - (p : ℤ_[p]) * ht₂

theorem exists_unit_eq_one_add_prime_pow_mul_pow (hp2 : p ≠ 2) (u : ℤ_[p]) (hu : IsUnit u) :
    ∃ (r : ℕ) (w : ℤ_[p]), u = (1 + (p : ℤ_[p])) ^ r * w ^ p := by
  obtain ⟨t, ht⟩ := exists_eq_pow_prime_mul_one_add u hu
  obtain ⟨c, s, hcs⟩ := exists_one_add_prime_mul_eq t
  obtain ⟨W, hW⟩ := exists_pow_prime_eq_one_add_prime_sq_mul hp2 s
  refine ⟨c, u * W, ?_⟩
  calc u = u ^ p * (1 + (p : ℤ_[p]) * t) := ht
    _ = u ^ p * ((1 + (p : ℤ_[p])) ^ c * (1 + (p : ℤ_[p]) ^ 2 * s)) := by rw [hcs]
    _ = (1 + (p : ℤ_[p])) ^ c * (u * W) ^ p := by rw [mul_pow, hW]; ring

end Padic.U6UnitsModPthPowersAux

theorem solution (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (a : ℚ_[p]) (ha : a ≠ 0) (hv : (p : ℤ) ∣ Padic.valuation a) :
    ∃ (r : ℕ) (w : ℚ_[p]), a = (1 + (p : ℚ_[p])) ^ r * w ^ p := by
  obtain ⟨m, hm⟩ := hv
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hp0' : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  set u : ℚ_[p] := a * (p : ℚ_[p]) ^ (-a.valuation) with hu_def
  have hu1 : ‖u‖ = 1 := by
    rw [hu_def, norm_mul, Padic.norm_eq_zpow_neg_valuation ha, Padic.norm_p_zpow, neg_neg,
      ← zpow_add₀ hp0', neg_add_cancel, zpow_zero]
  set U : ℤ_[p] := ⟨u, hu1.le⟩ with hU_def
  have hU : IsUnit U := PadicInt.isUnit_iff.mpr (by rw [PadicInt.norm_def]; exact hu1)
  obtain ⟨r, W, hW⟩ :=
    Padic.U6UnitsModPthPowersAux.exists_unit_eq_one_add_prime_pow_mul_pow hp2 U hU
  have hW' : u = (1 + (p : ℚ_[p])) ^ r * (W : ℚ_[p]) ^ p := by
    have h := congrArg ((↑) : ℤ_[p] → ℚ_[p]) hW
    simp only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_add, PadicInt.coe_one,
      PadicInt.coe_natCast] at h
    exact h
  have hau : a = u * (p : ℚ_[p]) ^ a.valuation := by
    rw [hu_def, mul_assoc, ← zpow_add₀ hp0, neg_add_cancel, zpow_zero, mul_one]
  refine ⟨r, (W : ℚ_[p]) * (p : ℚ_[p]) ^ m, ?_⟩
  rw [hau, hW', hm, zpow_mul', zpow_natCast]
  ring

end S_Padic_exists_eq_one_add_prime_pow_mul_pow_of_dvd_valuation
end P2MW
export P2MW.S_Padic_exists_eq_one_add_prime_pow_mul_pow_of_dvd_valuation (solution)
