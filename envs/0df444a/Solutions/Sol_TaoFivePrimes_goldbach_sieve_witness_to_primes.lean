-- Prove2me | solution 1 for TaoFivePrimes.goldbach_sieve_witness_to_primes
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-23T16:43:18.429785+00:00
-- url     : https://prove2.me/submissions/26ba630e-1081-43af-adcc-9ace171e9a14

import Mathlib

set_option autoImplicit false

theorem solution (n p q : ℕ)
    (hp : p.Prime) (hp5569 : p ≤ 5569) (hsum : p + q = n)
    (hq2 : 2 ≤ q) (hqN : q ≤ 4 * 10 ^ 14)
    (hsurv : ∀ r : ℕ, r.Prime → r ≤ 20000000 → r ∣ q → r = q) :
    ∃ p' q' : ℕ, p'.Prime ∧ q'.Prime ∧ p' + q' = n := by
  -- The survivor hypothesis forces q to be prime: its least prime factor
  -- q.minFac is a prime divisor of q with q.minFac ≤ √q ≤ 2·10⁷, so the
  -- survivor condition gives q.minFac = q, hence q is prime.
  have hq : q.Prime := by
    by_contra hnc
    have hne1 : q ≠ 1 := by omega
    have hmin : q.minFac.Prime := Nat.minFac_prime hne1
    have hdvd : q.minFac ∣ q := Nat.minFac_dvd q
    have hle : q.minFac ≤ 20000000 := by
      have hsq : q.minFac ^ 2 ≤ q := Nat.minFac_sq_le_self (by omega) hnc
      have hN : (20000000 : ℕ) ^ 2 = 4 * 10 ^ 14 := by norm_num
      have hqN' : q ≤ (20000000 : ℕ) ^ 2 := by rw [hN]; exact hqN
      by_contra h
      push Not at h
      have hlt : (20000000 : ℕ) ^ 2 < q.minFac ^ 2 :=
        pow_lt_pow_left₀ h (by norm_num) (by norm_num)
      omega
    have hmeq : q.minFac = q := hsurv q.minFac hmin hle hdvd
    rw [hmeq] at hmin
    exact hnc hmin
  exact ⟨p, q, hp, hq, hsum⟩
