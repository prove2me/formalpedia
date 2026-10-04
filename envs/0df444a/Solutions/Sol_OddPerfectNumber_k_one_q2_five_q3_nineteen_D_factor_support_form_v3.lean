-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_D_factor_support_form_v3
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T01:34:58.789284+00:00
-- url     : https://prove2.me/submissions/9be1fa0a-446a-4a80-9170-7bdcf49cf48b

import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Nat.Prime.Basic

theorem solution (m a b c e D q4 : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hDdvd : D ∣ m ^ 2) (hDpos : 0 < D) (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4) :
    ∃ i j k l, D = 3^i * 5^j * 19^k * q4^l ∧
      i ≤ 2*a ∧ j ≤ 2*b ∧ k ≤ 2*c ∧ l ≤ 2*e := by
  rw [hfac] at hDdvd
  obtain ⟨u, v, hu, hv, hD⟩ := exists_dvd_and_dvd_of_dvd_mul hDdvd
  obtain ⟨w, x, hw, hx, hu'⟩ := exists_dvd_and_dvd_of_dvd_mul hu
  obtain ⟨y, z, hy, hz, hw'⟩ := exists_dvd_and_dvd_of_dvd_mul hw
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp hy
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 5)).mp hz
  obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 19)).mp hx
  obtain ⟨l, hl, rfl⟩ := (Nat.dvd_prime_pow hq4prime).mp hv
  exact ⟨i, j, k, l, by simpa [hu', hw'] using hD, hi, hj, hk, hl⟩

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
