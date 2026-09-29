-- Prove2me | solution 1 for OddPerfectNumber.k_one_sigma_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T23:18:20.240001+00:00
-- url     : https://prove2.me/submissions/33089601-ba90-46a1-a174-d2c47b6e159e

import Mathlib

theorem solution (n p m : Nat) (hn : Nat.Perfect n) (hodd : Odd n)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hpm : ¬ p ∣ m) (hm_odd : Odd m) (h : n = p * m ^ 2) :
    (1 + p) * (∑ d ∈ (m ^ 2).divisors, d) = 2 * (p * m ^ 2) := by
  have hpos : 0 < n := hn.2
  have hsig : (∑ d ∈ n.divisors, d) = 2 * n :=
    (Nat.perfect_iff_sum_divisors_eq_two_mul hpos).mp hn
  rw [h] at hsig
  have hcop : Nat.Coprime p (m ^ 2) :=
    (hp.coprime_iff_not_dvd.mpr hpm).pow_right 2
  have hmult : ArithmeticFunction.sigma 1 (p * m ^ 2)
      = ArithmeticFunction.sigma 1 p * ArithmeticFunction.sigma 1 (m ^ 2) :=
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop.gcd_eq_one
  have hpsig : ArithmeticFunction.sigma 1 p = 1 + p := by
    have h1p : (1 : ℕ) ∉ ({p} : Finset ℕ) := by
      simp only [Finset.mem_singleton]
      exact Ne.symm hp.ne_one
    rw [ArithmeticFunction.sigma_one_apply, hp.divisors,
      Finset.sum_insert h1p, Finset.sum_singleton]
  rw [← ArithmeticFunction.sigma_one_apply] at hsig
  rw [hmult, hpsig, ArithmeticFunction.sigma_one_apply] at hsig
  exact hsig
