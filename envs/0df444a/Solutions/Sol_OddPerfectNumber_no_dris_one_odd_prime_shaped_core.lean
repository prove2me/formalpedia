-- Prove2me | solution 1 for OddPerfectNumber.no_dris_one_odd_prime_shaped_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T13:17:10.349297+00:00
-- url     : https://prove2.me/submissions/7f8626c1-834e-4fb9-a614-966053063a6b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_dris_packaged_absurd

open OddPerfectNumber

theorem solution (p k m s a q b : Nat)
    (hp : p.Prime) (hk : k ≠ 0) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hk1 : ((k + 1).primeFactors.erase 2).card ≤ 1)
    (hs2 : 2 ≤ s) (hs_not_even : ¬ Even s) (hs_not_prime : ¬ s.Prime)
    (hs_dvd : s ∣ m ^ 2)
    (hqp : q.Prime) (hshape : k + 1 = 2 ^ a * q ^ b) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  intro h
  obtain ⟨h1, h2⟩ := h
  have hprod_even : Even ((∑ d ∈ (p ^ k).divisors, d) * s) := by
    rw [← h1]
    exact even_two_mul (m ^ 2)
  have hsig_even : Even (∑ d ∈ (p ^ k).divisors, d) :=
    (Nat.even_mul.mp hprod_even).resolve_right hs_not_even
  obtain ⟨t, ht⟩ := hsig_even
  have hsig : (∑ d ∈ (p ^ k).divisors, d) = 2 * t := by omega
  have hcancel : 2 * m ^ 2 = 2 * (t * s) := by
    calc
      2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s := h1
      _ = (2 * t) * s := by rw [hsig]
      _ = 2 * (t * s) := by ring
  have hms : m ^ 2 = t * s := mul_left_cancel₀ two_ne_zero hcancel
  have hs_odd : Odd s := Nat.not_even_iff_odd.mp hs_not_even
  exact dris_packaged_absurd p k m s t s hp hm hpm hs_odd hsig hms h2
