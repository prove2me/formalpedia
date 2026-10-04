-- Prove2me | solution 1 for OddPerfectNumber.Kernel.source_exponent_at_least_two_when_p_divides_two_e_plus_one
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T02:18:42.25499+00:00
-- url     : https://prove2.me/submissions/ab724f28-72e9-4949-80da-fa54c96266e3

import Mathlib

theorem cex_2687a13f : ¬ (2 <= (3 : ℕ).factorization 3) := by
  rw [Nat.Prime.factorization_self Nat.prime_three]
  norm_num

theorem solution : ¬ (∀ {p t m : Nat}
    (hp : p.Prime) (hp4 : p % 4 = 1) (ht : t.Prime) (htd : t ∣ m) (hqp : t != p)
    (hgeom : p ∣ (∑ i ∈ Finset.range (2 * m.factorization t + 1), t ^ i)),
    2 <= m.factorization t) := by
  intro h
  apply cex_2687a13f
  apply @h 13 3 3 (by norm_num) (by norm_num) Nat.prime_three dvd_rfl (by decide)
  rw [Nat.Prime.factorization_self Nat.prime_three]
  decide
