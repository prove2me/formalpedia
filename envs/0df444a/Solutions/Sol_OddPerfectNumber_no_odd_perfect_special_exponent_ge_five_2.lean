-- Prove2me | solution 2 for OddPerfectNumber.no_odd_perfect_special_exponent_ge_five
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T23:46:05.630693+00:00
-- url     : https://prove2.me/submissions/ae26dac9-745c-4762-a4f9-6f58286b3e48
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_no_euler_equation_special_exponent_five
import Theorems.Thm_OddPerfectNumber_no_euler_equation_special_exponent_ge_nine

open OddPerfectNumber

theorem solution (n p k m : Nat) (hn : Nat.Perfect n) (hodd : Odd n)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hk5 : 5 ≤ k) (hpm : ¬ p ∣ m) :
    n ≠ p ^ k * m ^ 2 := by
  intro h
  -- Since n is odd and n = p ^ k * m ^ 2, m must be odd.
  have hm : Odd m := by
    by_contra hcon
    have hev : Even m := Nat.not_odd_iff_even.mp hcon
    have e1 : Even (m ^ 2) := Nat.even_pow.mpr ⟨hev, by decide⟩
    have e2 : Even (p ^ k * m ^ 2) := Nat.even_mul.mpr (Or.inr e1)
    rw [← h] at e2
    exact (Nat.not_even_iff_odd.mpr hodd) e2
  -- Positivity of n from the Euler form.
  have hnpos : 0 < n := by
    have h1 : 0 < p ^ k := pow_pos hp.pos k
    have h2 : 0 < m ^ 2 := pow_pos hm.pos 2
    rw [h]
    exact mul_pos h1 h2
  -- Perfection gives the divisor-sum equation for n.
  have hsig : ∑ d ∈ n.divisors, d = 2 * n :=
    (Nat.perfect_iff_sum_divisors_eq_two_mul hnpos).mp hn
  -- The Euler factors are coprime, so sigma splits multiplicatively.
  have hcm : Nat.Coprime p m := hp.coprime_iff_not_dvd.mpr hpm
  have hkpos : 0 < k := by omega
  have h2pos : 0 < 2 := by decide
  have hcop : Nat.Coprime (p ^ k) (m ^ 2) := by
    rw [Nat.coprime_pow_left_iff hkpos, Nat.coprime_pow_right_iff h2pos]
    exact hcm
  rw [h, Nat.Coprime.sum_divisors_mul hcop] at hsig
  -- Since k ≡ 1 mod 4 and k ≥ 5, either k = 5 or k ≥ 9.
  rcases (by omega : k = 5 ∨ 9 ≤ k) with rfl | hk9
  · exact no_euler_equation_special_exponent_five p m hp hp4 hm hpm hsig
  · exact no_euler_equation_special_exponent_ge_nine p k m hp hp4 hk4 hk9 hm hpm hsig
