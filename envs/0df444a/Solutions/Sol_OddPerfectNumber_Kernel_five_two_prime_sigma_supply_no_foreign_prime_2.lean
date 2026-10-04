-- Prove2me | solution 2 for OddPerfectNumber.Kernel.five_two_prime_sigma_supply_no_foreign_prime
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T07:44:23.63199+00:00
-- url     : https://prove2.me/submissions/38550819-1840-4306-b7ac-670a89bb5ce3

import Mathlib

theorem solution {p m d1 q r : Nat} (hp : p.Prime)
    (hq : q.Prime) (hr : r.Prime)
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * (d1 ^ 2 * (q * r))) :
    forall t : Nat, t.Prime -> Dvd.dvd t (∑ d ∈ (m ^ 2).divisors, d) ->
      (t = p \/ Dvd.dvd t d1 \/ t = q \/ t = r) := by
  intro t ht hdvd
  rw [h2] at hdvd
  rcases (Nat.Prime.dvd_mul ht).1 hdvd with h | h
  · left
    exact (Nat.prime_dvd_prime_iff_eq ht hp).1 (ht.dvd_of_dvd_pow h)
  · rcases (Nat.Prime.dvd_mul ht).1 h with h | h
    · right; left
      exact ht.dvd_of_dvd_pow h
    · rcases (Nat.Prime.dvd_mul ht).1 h with h | h
      · right; right; left
        exact (Nat.prime_dvd_prime_iff_eq ht hq).1 h
      · right; right; right
        exact (Nat.prime_dvd_prime_iff_eq ht hr).1 h

#print axioms solution
