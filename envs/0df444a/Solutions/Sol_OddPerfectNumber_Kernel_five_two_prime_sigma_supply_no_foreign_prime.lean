-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_two_prime_sigma_supply_no_foreign_prime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T07:38:28.408981+00:00
-- url     : https://prove2.me/submissions/d630d3ff-caa6-43e7-91e4-a170a5c31ed3

-- Target: OddPerfectNumber.Kernel.five_two_prime_sigma_supply_no_foreign_prime
--
-- `h2` reads `sigma(m^2) = p^5 * (d1^2 * (q*r))`.  A prime `t` dividing the left side divides
-- the right.  The product is `p^5 * (d1^2 * (q*r))`, so the splits must follow that shape
-- exactly: first `t | p^5` or `t | (d1^2*(q*r))`, then `t | d1^2` or `t | (q*r)`, then
-- `t | q` or `t | r`.
--
-- REPAIR of 6832 (1 group, complete 91-line capture read).  Cause: the proof used
-- `dvd_mul_of_dvd_left hdvd (d1^2*(q*r))`, which yields `t | (p^5 * (d1^2*(q*r))) * (d1^2*(q*r))`
-- by APPENDING, so the inner `dvd_mul.mp` then saw a product whose left factor was that whole
-- product, and the `t | p^5` branch was therefore handed `t | p^5*(d1^2*(q*r))` instead of
-- `t | p^5`.  Using `ht.dvd_mul.mp hdvd` directly (no extra `dvd_mul_of_dvd_left`) makes the
-- first split see the true shape.
import Mathlib

theorem solution {p m d1 q r : Nat} (hp : p.Prime)
    (hq : q.Prime) (hr : r.Prime)
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * (d1 ^ 2 * (q * r))) :
    forall t : Nat, t.Prime -> Dvd.dvd t (∑ d ∈ (m ^ 2).divisors, d) ->
      (t = p \/ Dvd.dvd t d1 \/ t = q \/ t = r) := by
  intro t ht hts
  have hdvd : Dvd.dvd t (p ^ 5 * (d1 ^ 2 * (q * r))) := by rwa [← h2]
  rcases ht.dvd_mul.mp hdvd with h1 | h2'
  · left
    exact (Nat.prime_dvd_prime_iff_eq ht hp).mp (ht.dvd_of_dvd_pow h1)
  · rcases ht.dvd_mul.mp h2' with hd | hr'
    · right; left
      exact ht.dvd_of_dvd_pow hd
    · rcases ht.dvd_mul.mp hr' with hq' | hr''
      · right; right; left
        exact (Nat.prime_dvd_prime_iff_eq ht hq).mp hq'
      · right; right; right
        exact (Nat.prime_dvd_prime_iff_eq ht hr).mp hr''
