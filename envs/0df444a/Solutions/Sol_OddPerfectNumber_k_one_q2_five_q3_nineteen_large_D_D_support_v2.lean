-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_large_D_D_support_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T17:32:29.092668+00:00
-- url     : https://prove2.me/submissions/17f2fb0b-cb47-45f6-9b46-b0b888089d3a

import Mathlib

theorem solution (m a b c e D q4 : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hDdvd : D ∣ m ^ 2)
    (hq4prime : q4.Prime) :
    ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4 := by
  intro r hr hrd
  have hrm : r ∣ m ^ 2 := dvd_trans hrd hDdvd
  rw [hfac] at hrm
  rcases (hr.dvd_mul).mp hrm with hr123 | hrq
  · rcases (hr.dvd_mul).mp hr123 with hr12 | hr19
    · rcases (hr.dvd_mul).mp hr12 with hr3 | hr5
      · have hr3' : r ∣ 3 := hr.dvd_of_dvd_pow hr3
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hr3' with h1 | h3
        · have hrge : 2 ≤ r := hr.two_le
          omega
        · exact Or.inl h3
      · have hr5' : r ∣ 5 := hr.dvd_of_dvd_pow hr5
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hr5' with h1 | h5
        · have hrge : 2 ≤ r := hr.two_le
          omega
        · exact Or.inr (Or.inl h5)
    · have hr19' : r ∣ 19 := hr.dvd_of_dvd_pow hr19
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 19)).mp hr19' with h1 | h19
      · have hrge : 2 ≤ r := hr.two_le
        omega
      · exact Or.inr (Or.inr (Or.inl h19))
  · have hrq' : r ∣ q4 := hr.dvd_of_dvd_pow hrq
    exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hr hq4prime).mp hrq')))
