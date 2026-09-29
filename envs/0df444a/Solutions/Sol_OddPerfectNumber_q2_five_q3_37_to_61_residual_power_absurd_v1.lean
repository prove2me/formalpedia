-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_37_to_61_residual_power_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T16:57:14.23297+00:00
-- url     : https://prove2.me/submissions/99c232d7-9f68-4897-918c-efef9d02dcf8

import Mathlib

theorem solution (q4 t S beta : Nat)
    (hcase :
      (q4 = 47 ∧ t = 23 ∧ S % q4 ^ 2 = 1786) ∨
      (q4 = 59 ∧ t = 29 ∧ S % q4 ^ 2 = 1475) ∨
      (q4 = 83 ∧ t = 41 ∧ S % q4 ^ 2 = 1328) ∨
      (q4 = 107 ∧ t = 53 ∧ S % q4 ^ 2 = 8346) ∨
      (q4 = 167 ∧ t = 83 ∧ S % q4 ^ 2 = 23714) ∨
      (q4 = 179 ∧ t = 89 ∧ S % q4 ^ 2 = 12172) ∨
      (q4 = 227 ∧ t = 113 ∧ S % q4 ^ 2 = 10896) ∨
      (q4 = 263 ∧ t = 131 ∧ S % q4 ^ 2 = 31560))
    (hsum : S = q4 ^ beta) (hbeta : 2 ≤ beta) : False := by
  rcases hcase with h | h | h | h | h | h | h | h
  · rcases h with ⟨hq, _, hrem⟩
    subst q4
    rw [hsum] at hrem
    have hpow : 47 ^ 2 ∣ 47 ^ beta := by exact Nat.pow_dvd_pow 47 (by omega)
    have : (47 ^ beta) % (47 ^ 2) = 0 := Nat.dvd_iff_mod_eq_zero.mp hpow
    norm_num at hrem this
    omega
  · rcases h with ⟨hq, _, hrem⟩
    subst q4
    rw [hsum] at hrem
    have hpow : 59 ^ 2 ∣ 59 ^ beta := by exact Nat.pow_dvd_pow 59 (by omega)
    have : (59 ^ beta) % (59 ^ 2) = 0 := Nat.dvd_iff_mod_eq_zero.mp hpow
    norm_num at hrem this
    omega
  · rcases h with ⟨hq, _, hrem⟩
    subst q4
    rw [hsum] at hrem
    have hpow : 83 ^ 2 ∣ 83 ^ beta := by exact Nat.pow_dvd_pow 83 (by omega)
    have : (83 ^ beta) % (83 ^ 2) = 0 := Nat.dvd_iff_mod_eq_zero.mp hpow
    norm_num at hrem this
    omega
  · rcases h with ⟨hq, _, hrem⟩
    subst q4
    rw [hsum] at hrem
    have hpow : 107 ^ 2 ∣ 107 ^ beta := by exact Nat.pow_dvd_pow 107 (by omega)
    have : (107 ^ beta) % (107 ^ 2) = 0 := Nat.dvd_iff_mod_eq_zero.mp hpow
    norm_num at hrem this
    omega
  · rcases h with ⟨hq, _, hrem⟩
    subst q4
    rw [hsum] at hrem
    have hpow : 167 ^ 2 ∣ 167 ^ beta := by exact Nat.pow_dvd_pow 167 (by omega)
    have : (167 ^ beta) % (167 ^ 2) = 0 := Nat.dvd_iff_mod_eq_zero.mp hpow
    norm_num at hrem this
    omega
  · rcases h with ⟨hq, _, hrem⟩
    subst q4
    rw [hsum] at hrem
    have hpow : 179 ^ 2 ∣ 179 ^ beta := by exact Nat.pow_dvd_pow 179 (by omega)
    have : (179 ^ beta) % (179 ^ 2) = 0 := Nat.dvd_iff_mod_eq_zero.mp hpow
    norm_num at hrem this
    omega
  · rcases h with ⟨hq, _, hrem⟩
    subst q4
    rw [hsum] at hrem
    have hpow : 227 ^ 2 ∣ 227 ^ beta := by exact Nat.pow_dvd_pow 227 (by omega)
    have : (227 ^ beta) % (227 ^ 2) = 0 := Nat.dvd_iff_mod_eq_zero.mp hpow
    norm_num at hrem this
    omega
  · rcases h with ⟨hq, _, hrem⟩
    subst q4
    rw [hsum] at hrem
    have hpow : 263 ^ 2 ∣ 263 ^ beta := by exact Nat.pow_dvd_pow 263 (by omega)
    have : (263 ^ beta) % (263 ^ 2) = 0 := Nat.dvd_iff_mod_eq_zero.mp hpow
    norm_num at hrem this
    omega
