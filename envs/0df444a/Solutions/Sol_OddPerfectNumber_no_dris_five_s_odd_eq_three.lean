-- Prove2me | solution 1 for OddPerfectNumber.no_dris_five_s_odd_eq_three
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T08:27:01.617524+00:00
-- url     : https://prove2.me/submissions/6e45e28e-5815-44b1-94d2-45f08d5d62a5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_sigma_prime_pow_even
import Theorems.Thm_OddPerfectNumber_dris_packaged_absurd

open OddPerfectNumber

theorem solution (p m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m) (hs3 : s = 3) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * s) := by
  subst hs3
  intro h
  obtain ⟨h1, h2⟩ := h
  have hp2' : p ≠ 2 := by
    intro hcon
    subst hcon
    simp at hp2
  obtain ⟨t, ht⟩ := sigma_prime_pow_even p 5 hp hp2' (by decide)
  have hsig : (∑ d ∈ (p ^ 5).divisors, d) = 2 * t := by omega
  have hcancel : 2 * m ^ 2 = 2 * (t * 3) := by
    calc 2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * 3 := h1
      _ = (2 * t) * 3 := by rw [hsig]
      _ = 2 * (t * 3) := by ring
  have hms : m ^ 2 = t * 3 := mul_left_cancel₀ two_ne_zero hcancel
  have hs_odd : Odd 3 := by decide
  exact dris_packaged_absurd p 5 m 3 t 3 hp hm hpm hs_odd hsig hms h2
