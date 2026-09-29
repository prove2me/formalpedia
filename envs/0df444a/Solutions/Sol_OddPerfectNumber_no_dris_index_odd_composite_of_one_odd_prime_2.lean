-- Prove2me | solution 2 for OddPerfectNumber.no_dris_index_odd_composite_of_one_odd_prime
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T11:58:06.457324+00:00
-- url     : https://prove2.me/submissions/90da910c-51af-40e5-849e-06dd0d9250bf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_no_dris_one_odd_prime_core

theorem _root_.solution (p k m s : Nat)
    (hp : p.Prime) (hk : k ≠ 0) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hk1 : ((k + 1).primeFactors.erase 2).card ≤ 1)
    (hs2 : 2 ≤ s) (hs_not_even : ¬ Even s) (hs_not_prime : ¬ s.Prime) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  intro h
  have hs_dvd : s ∣ m ^ 2 := by
    have hodd : Odd s := (Nat.even_or_odd s).resolve_left hs_not_even
    have hcop : Nat.Coprime s 2 := Nat.coprime_two_right.2 hodd
    have hd2 : s ∣ m ^ 2 * 2 :=
      ⟨∑ d ∈ (p ^ k).divisors, d, by rw [mul_comm (m ^ 2) 2, h.1]; ring⟩
    exact Nat.Coprime.dvd_of_dvd_mul_right hcop hd2
  exact OddPerfectNumber.no_dris_one_odd_prime_core p k m s hp hk hm hpm hk1 hs2
    hs_not_even hs_not_prime hs_dvd h

#print axioms solution
