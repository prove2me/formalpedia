-- Prove2me | solution 1 for OddPerfectNumber.no_euler_equation_special_exponent_five
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-08T22:36:48.765291+00:00
-- url     : https://prove2.me/submissions/cc63691f-81a9-41b4-bba2-b6ca5278d065
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_dris_parametrisation
import Theorems.Thm_OddPerfectNumber_sigma_prime_pow_ne_two_mul_sq_of_six_dvd
import Theorems.Thm_OddPerfectNumber_no_dris_special_exponent_five_s_ge_two

open Finset OddPerfectNumber

theorem solution (p m : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hm : Odd m) (hpm : ¬ p ∣ m) :
    (∑ d ∈ (p ^ 5).divisors, d) * (∑ d ∈ (m ^ 2).divisors, d) ≠ 2 * (p ^ 5 * m ^ 2) := by
  intro heq
  have hp2 : p ≠ 2 := by
    intro hp_eq_two
    subst p
    norm_num at hp4
  have hOdd : Odd m := hm
  obtain ⟨t, hm_eq⟩ := hm
  have hm_nonzero : m ≠ 0 := by
    omega
  rcases dris_parametrisation p 5 m hp hp2 (by norm_num) hm_nonzero heq with
    ⟨s, hs_pos, h_two, h_sigma⟩
  have hs_ne_one : s ≠ 1 := by
    intro hs_eq_one
    have hsigma_two : (∑ d ∈ (p ^ 5).divisors, d) = 2 * m ^ 2 := by
      rw [hs_eq_one, mul_one] at h_two
      exact h_two.symm
    exact (sigma_prime_pow_ne_two_mul_sq_of_six_dvd p 5 m hp hp2 (by norm_num)) hsigma_two
  have hs_ge_two : 2 ≤ s := by
    omega
  exact (no_dris_special_exponent_five_s_ge_two p m s hp hp2 hp4 hOdd hpm hs_ge_two
    ⟨h_two, h_sigma⟩)
