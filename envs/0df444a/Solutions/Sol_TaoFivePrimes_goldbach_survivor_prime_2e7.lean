-- Prove2me | solution 1 for TaoFivePrimes.goldbach_survivor_prime_2e7
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-23T16:45:35.387544+00:00
-- url     : https://prove2.me/submissions/7313bc10-cf94-4ee8-8d17-f298fac7685f

import Mathlib

set_option autoImplicit false

-- Proof of TaoFivePrimes.goldbach_survivor_prime_2e7:
-- a sieve survivor n with 2 ≤ n ≤ (2·10^7)^2 is prime.
-- Strategy: by_contra. If n is not prime, n.minFac is a prime divisor,
-- and minFac n ^ 2 ≤ n (Nat.minFac_sq_le_self), so
-- minFac n ≤ sqrt n ≤ sqrt (4·10^14) = 20000000,
-- contradicting the survivor hypothesis.
-- NOTE: the server soundness guard rejects `native_decide`, so the
-- sqrt value is proved by hand (kernel-checked, norm_num arithmetic).
theorem solution (n : ℕ) (h2 : 2 ≤ n) (hN : n ≤ 4 * 10 ^ 14)
    (hsurv : ∀ p : ℕ, p.Prime → p ≤ 20000000 → ¬ p ∣ n) :
    n.Prime := by
  by_contra hnot
  have hmf_prime : (n.minFac).Prime := Nat.minFac_prime (by omega)
  have hmf_dvd : n.minFac ∣ n := Nat.minFac_dvd n
  have hmf_sq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnot
  have hmf_le : n.minFac ≤ n.sqrt := (Nat.le_sqrt').mpr hmf_sq
  have hsqrtval : (4 * 10 ^ 14).sqrt = 20000000 := by
    apply le_antisymm
    · by_contra hlt
      push_neg at hlt
      have h1 : (20000001 : ℕ) ^ 2 ≤ ((4 * 10 ^ 14).sqrt) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
      have h2 : ((4 * 10 ^ 14).sqrt) ^ 2 ≤ 4 * 10 ^ 14 := Nat.sqrt_le' _
      have h3 : (20000001 : ℕ) ^ 2 ≤ 4 * 10 ^ 14 := le_trans h1 h2
      norm_num at h3
    · exact (Nat.le_sqrt').mpr (by norm_num)
  have hsqrtN : n.sqrt ≤ (4 * 10 ^ 14).sqrt := Nat.sqrt_le_sqrt hN
  have hle : n.minFac ≤ 20000000 :=
    le_trans (le_trans hmf_le hsqrtN) (le_of_eq hsqrtval)
  exact hsurv _ hmf_prime hle hmf_dvd
