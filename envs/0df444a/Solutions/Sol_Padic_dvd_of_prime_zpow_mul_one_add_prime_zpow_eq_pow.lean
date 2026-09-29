-- Prove2me | solution 1 for Padic.dvd_of_prime_zpow_mul_one_add_prime_zpow_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/e2bcd25e-dbdb-5626-9dba-9bc901f0d5c7

import Mathlib
import Theorems.Thm_PadicInt_dvd_of_one_add_prime_pow_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Padic_dvd_of_prime_zpow_mul_one_add_prime_zpow_eq_pow

open Polynomial

namespace Ws26U4

theorem exists_one_add_pow_eq_cubic {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    ∃ d : R, (1 + x) ^ n = 1 + n * x + (n.choose 2 : R) * x ^ 2 + x ^ 3 * d := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨(n.choose 2 : R) + d + x * d, ?_⟩
    rw [pow_succ, hd, Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    ring

theorem exists_one_add_pow_eq_quadratic {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    ∃ c : R, (1 + x) ^ n = 1 + n * x + x ^ 2 * c := by
  obtain ⟨d, hd⟩ := exists_one_add_pow_eq_cubic x n
  exact ⟨(n.choose 2 : R) + x * d, by rw [hd]; ring⟩

end Ws26U4

namespace Ws26U4

section IntBasic
open PadicInt

variable {p : ℕ} [hp : Fact p.Prime]

theorem toZMod_natCast_self : toZMod (p : ℤ_[p]) = 0 := by
  rw [map_natCast, ZMod.natCast_self]

theorem toZModPow_natCast_self_pow (n : ℕ) : toZModPow n ((p : ℤ_[p]) ^ n) = 0 := by
  rw [map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self]

theorem norm_eq_one_of_toZMod_ne_zero {z : ℤ_[p]} (hz : toZMod z ≠ 0) : ‖z‖ = 1 := by
  rcases lt_or_eq_of_le (norm_le_one z) with h | h
  · exfalso
    apply hz
    rw [← RingHom.mem_ker, ker_toZMod, IsLocalRing.mem_maximalIdeal, mem_nonunits]
    exact h
  · exact h

theorem norm_eq_one_of_toZMod_eq_one {z : ℤ_[p]} (hz : toZMod z = 1) : ‖z‖ = 1 :=
  norm_eq_one_of_toZMod_ne_zero (by rw [hz]; exact one_ne_zero)

theorem exists_eq_one_add_prime_mul_of_toZMod_eq_one {z : ℤ_[p]} (hz : toZMod z = 1) :
    ∃ b : ℤ_[p], z = 1 + p * b := by
  have hker : z - 1 ∈ RingHom.ker (toZMod (p := p)) := by
    rw [RingHom.mem_ker, map_sub, hz, map_one, sub_self]
  rw [ker_toZMod, maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hker
  obtain ⟨b, hb⟩ := hker
  exact ⟨b, by rw [← hb]; ring⟩

theorem exists_eq_one_add_prime_sq_mul_of_toZModPow_two_eq_one {u : ℤ_[p]}
    (hu : toZModPow 2 u = 1) : ∃ b : ℤ_[p], u = 1 + (p : ℤ_[p]) ^ 2 * b := by
  have hker : u - 1 ∈ RingHom.ker (toZModPow (p := p) 2) := by
    rw [RingHom.mem_ker, map_sub, hu, map_one, sub_self]
  rw [ker_toZModPow, Ideal.mem_span_singleton] at hker
  obtain ⟨b, hb⟩ := hker
  exact ⟨b, by rw [← hb]; ring⟩

theorem toZMod_one_add_prime : toZMod (1 + p : ℤ_[p]) = 1 := by
  rw [map_add, map_one, toZMod_natCast_self, add_zero]

theorem toZModPow_two_one_add_prime_pow (j : ℕ) :
    toZModPow 2 ((1 + p : ℤ_[p]) ^ j) = 1 + (j : ZMod (p ^ 2)) * p := by
  obtain ⟨c, hc⟩ := exists_one_add_pow_eq_quadratic (p : ℤ_[p]) j
  rw [hc, map_add, map_add, map_mul, map_one, map_mul, map_natCast, map_natCast,
    toZModPow_natCast_self_pow, zero_mul, add_zero]

end IntBasic

end Ws26U4

namespace Ws26U4
section RatBasic
open Padic
variable {p : ℕ} [hp : Fact p.Prime]

theorem natCast_prime_ne_zero : ((p : ℚ_[p])) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero

theorem coe_one_add_prime : ((1 + p : ℤ_[p]) : ℚ_[p]) = 1 + p := by push_cast; rfl

theorem norm_one_add_prime : ‖(1 + p : ℚ_[p])‖ = 1 := by
  rw [← coe_one_add_prime]
  exact norm_eq_one_of_toZMod_eq_one toZMod_one_add_prime

theorem one_add_prime_ne_zero : (1 + p : ℚ_[p]) ≠ 0 := by
  intro h
  have h1 := norm_one_add_prime (p := p)
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

theorem exists_norm_eq_one_and_eq_zpow_mul {x : ℚ_[p]} (hx : x ≠ 0) :
    ∃ u : ℚ_[p], ‖u‖ = 1 ∧ x = (p : ℚ_[p]) ^ x.valuation * u := by
  refine ⟨(p : ℚ_[p]) ^ (-x.valuation) * x, ?_, ?_⟩
  · rw [norm_mul, norm_p_zpow, neg_neg, norm_eq_zpow_neg_valuation hx, ← zpow_add₀
      (by exact_mod_cast hp.out.pos.ne' : ((p : ℝ)) ≠ 0), add_neg_cancel, zpow_zero]
  · rw [← mul_assoc, ← zpow_add₀ natCast_prime_ne_zero, add_neg_cancel, zpow_zero, one_mul]

theorem valuation_eq_zero_of_norm_eq_one {u : ℚ_[p]} (hu : ‖u‖ = 1) : u.valuation = 0 := by
  have hu0 : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu; exact one_ne_zero hu.symm
  have h := norm_eq_zpow_neg_valuation hu0
  rw [hu] at h
  have hbase0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hbase1 : ((p : ℝ)) ≠ 1 := by exact_mod_cast hp.out.one_lt.ne'
  have := (zpow_right_inj₀ hbase0 hbase1).mp (h.symm.trans (zpow_zero _).symm)
  omega

theorem norm_eq_one_of_norm_pow_eq_one {y : ℚ_[p]} {n : ℕ} (hn : n ≠ 0)
    (h : ‖y ^ n‖ = 1) : ‖y‖ = 1 := by
  rw [norm_pow] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg y) hn).mp h

end RatBasic
end Ws26U4

namespace Ws26U4
section RatIndep
open Padic
variable {p : ℕ} [hp : Fact p.Prime]

theorem dvd_of_one_add_prime_pow_eq_pow_rat {n : ℕ} {w : ℚ_[p]}
    (h : (1 + p : ℚ_[p]) ^ n = w ^ p) : p ∣ n := by
  have hw : ‖w‖ = 1 :=
    norm_eq_one_of_norm_pow_eq_one hp.out.ne_zero (by rw [← h, norm_pow, norm_one_add_prime, one_pow])
  set wInt : ℤ_[p] := ⟨w, le_of_eq hw⟩ with hwInt_def
  have hInt : (1 + p : ℤ_[p]) ^ n = wInt ^ p := by
    apply Subtype.ext
    push_cast [hwInt_def]
    exact h
  exact PadicInt.dvd_of_one_add_prime_pow_eq_pow hInt

theorem dvd_of_one_add_prime_zpow_eq_pow {j : ℤ} {w : ℚ_[p]}
    (h : (1 + p : ℚ_[p]) ^ j = w ^ p) : (p : ℤ) ∣ j := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, j = n ∨ j = -n := ⟨j.natAbs, Int.natAbs_eq j⟩
  rcases hn with rfl | rfl
  · rw [zpow_natCast] at h
    exact Int.natCast_dvd_natCast.mpr (dvd_of_one_add_prime_pow_eq_pow_rat h)
  · rw [dvd_neg]
    refine Int.natCast_dvd_natCast.mpr (dvd_of_one_add_prime_pow_eq_pow_rat (w := w⁻¹) ?_)
    rw [inv_pow, ← h, zpow_neg, zpow_natCast, inv_inv]

end RatIndep
end Ws26U4

open Ws26U4 Padic in
theorem solution {p : ℕ} [hp : Fact p.Prime]
    {i j : ℤ} {y : ℚ_[p]}
    (h : (p : ℚ_[p]) ^ i * (1 + p : ℚ_[p]) ^ j = y ^ p) :
    (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j := by

  have hval : i = p * y.valuation := by
    have h1 : ((p : ℚ_[p]) ^ i * (1 + p : ℚ_[p]) ^ j).valuation = i := by
      rw [valuation_mul (zpow_ne_zero _ natCast_prime_ne_zero)
          (zpow_ne_zero _ one_add_prime_ne_zero),
        valuation_zpow, valuation_zpow, valuation_eq_zero_of_norm_eq_one norm_one_add_prime,
        mul_zero, add_zero, valuation_p, mul_one]
    rw [h, valuation_pow] at h1
    exact h1.symm
  have hi : (p : ℤ) ∣ i := ⟨y.valuation, hval⟩
  refine ⟨hi, ?_⟩
  obtain ⟨q, hq⟩ := hi

  have e3 : ((p : ℚ_[p]) ^ (-q)) ^ p = ((p : ℚ_[p]) ^ i)⁻¹ := by
    rw [← zpow_natCast ((p : ℚ_[p]) ^ (-q)), ← zpow_mul, neg_mul, zpow_neg, hq, mul_comm]
  refine dvd_of_one_add_prime_zpow_eq_pow (w := y * (p : ℚ_[p]) ^ (-q)) ?_
  calc (1 + p : ℚ_[p]) ^ j
      = ((p : ℚ_[p]) ^ i)⁻¹ * ((p : ℚ_[p]) ^ i * (1 + p : ℚ_[p]) ^ j) := by
        rw [← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ natCast_prime_ne_zero), one_mul]
    _ = ((p : ℚ_[p]) ^ i)⁻¹ * y ^ p := by rw [h]
    _ = (y * (p : ℚ_[p]) ^ (-q)) ^ p := by rw [mul_pow, e3]; ring

end S_Padic_dvd_of_prime_zpow_mul_one_add_prime_zpow_eq_pow
end P2MW
export P2MW.S_Padic_dvd_of_prime_zpow_mul_one_add_prime_zpow_eq_pow (solution)
