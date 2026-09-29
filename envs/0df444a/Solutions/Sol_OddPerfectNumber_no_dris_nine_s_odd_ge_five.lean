-- Prove2me | solution 1 for OddPerfectNumber.no_dris_nine_s_odd_ge_five
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T08:57:21.395627+00:00
-- url     : https://prove2.me/submissions/28328953-86e1-4f78-9758-ab6934c83999
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_sigma_prime_pow_even
import Theorems.Thm_OddPerfectNumber_dris_packaged_absurd

open OddPerfectNumber

theorem solution (p k m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hk9 : k = 9) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hs5 : 5 ≤ s) (hs_not_even : ¬ Even s) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  subst hk9
  intro h
  obtain ⟨h1, h2⟩ := h
  have hp2' : p ≠ 2 := by
    intro hcon
    subst hcon
    simp at hp2
  obtain ⟨t, ht⟩ := sigma_prime_pow_even p 9 hp hp2' (by decide)
  have hsig : (∑ d ∈ (p ^ 9).divisors, d) = 2 * t := by omega
  have hcancel : 2 * m ^ 2 = 2 * (t * s) := by
    calc 2 * m ^ 2 = (∑ d ∈ (p ^ 9).divisors, d) * s := h1
      _ = (2 * t) * s := by rw [hsig]
      _ = 2 * (t * s) := by ring
  have hms : m ^ 2 = t * s := mul_left_cancel₀ two_ne_zero hcancel
  have hs_odd : Odd s := Nat.not_even_iff_odd.mp hs_not_even
  exact dris_packaged_absurd p 9 m s t s hp hm hpm hs_odd hsig hms h2
