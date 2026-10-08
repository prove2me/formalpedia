-- Prove2me | solution 1 for OddPerfectNumber.Kernel.three_geom_sum_prime_divisors_one_or_eleven_mod_twelve
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T06:01:12.767319+00:00
-- url     : https://prove2.me/submissions/3fca9f6f-89fa-4fbd-9558-e60515d92fc0

import Mathlib

set_option autoImplicit false

theorem solution (e l : Nat)
    (hl : l.Prime) (hl3 : l != 3)
    (hld : Dvd.dvd l (∑ i ∈ Finset.range (2 * e + 1), (3 : Nat) ^ i)) :
    (l % 12 = 1 \/ l % 12 = 11) := by
  have := Fact.mk hl
  have hl3' : l ≠ 3 := by simpa using hl3
  have hmod2 : (∑ i ∈ Finset.range (2 * e + 1), (3 : Nat) ^ i) % 2 = 1 := by
    rw [Finset.sum_nat_mod]
    simp [Nat.pow_mod]
  have hl2 : l ≠ 2 := by
    rintro rfl
    obtain ⟨c, hc⟩ := hld
    omega
  have hz : ((∑ i ∈ Finset.range (2 * e + 1), (3 : Nat) ^ i : ℕ) : ZMod l) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hld
  push_cast at hz
  have hpow : (3 : ZMod l) ^ (2 * e + 1) = 1 := by
    have := geom_sum_mul (3 : ZMod l) (2 * e + 1)
    rw [hz, zero_mul] at this
    exact (sub_eq_zero.mp this.symm)
  have hsq : IsSquare ((3 : ℕ) : ZMod l) := by
    refine ⟨3 ^ (e + 1), ?_⟩
    rw [← pow_add, show e + 1 + (e + 1) = (2 * e + 1) + 1 by ring, pow_succ, hpow, one_mul]
    norm_num
  have hl3mod : l % 3 ≠ 0 := by
    intro h
    have : 3 ∣ l := Nat.dvd_of_mod_eq_zero h
    rcases (Nat.Prime.eq_one_or_self_of_dvd hl 3 this) with h' | h' <;> omega
  have hcast : ((l : ℕ) : ZMod 3) = ((l % 3 : ℕ) : ZMod 3) := (ZMod.natCast_mod l 3).symm
  have hodd : l % 2 = 1 := (hl.eq_two_or_odd).resolve_left hl2
  have h4 : l % 4 = 1 ∨ l % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · have h := (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := l) (q := 3) h4 (by decide)).mp hsq
    rw [hcast] at h
    have : l % 3 = 1 := by
      have hlt : l % 3 < 3 := Nat.mod_lt _ (by norm_num)
      interval_cases h3 : l % 3
      · exact absurd rfl hl3mod
      · rfl
      · exfalso; revert h; decide
    omega
  · have h := (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three (p := l) (q := 3) h4 (by decide) hl3').mp hsq
    rw [hcast] at h
    have : l % 3 = 2 := by
      have hlt : l % 3 < 3 := Nat.mod_lt _ (by norm_num)
      interval_cases h3 : l % 3
      · exact absurd rfl hl3mod
      · exfalso; apply h; decide
      · rfl
    omega
