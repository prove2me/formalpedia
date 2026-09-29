-- Prove2me | solution 1 for OddPerfectNumber.no_dris_thirteen_witnessed_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T13:15:50.074537+00:00
-- url     : https://prove2.me/submissions/6547fedc-c6a8-47ba-96b3-ee0746d400ad
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_sigma_prime_pow_even
import Theorems.Thm_OddPerfectNumber_dris_packaged_absurd

open OddPerfectNumber

theorem solution (p k m s q1 q2 : Nat)
    (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hk13 : 13 ≤ k) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hs2 : 2 ≤ s) (hs_not_even : ¬ Even s)
    (hq1ne : q1 ≠ q2) (hq1p : q1.Prime) (hq2p : q2.Prime)
    (hq1o : Odd q1) (hq2o : Odd q2) (hq1d : q1 ∣ k + 1) (hq2d : q2 ∣ k + 1)
    (hs_dvd : s ∣ m ^ 2) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  intro h
  obtain ⟨h1, h2⟩ := h
  have hp2' : p ≠ 2 := by
    intro hcon
    subst hcon
    simp at hp2
  obtain ⟨t, ht⟩ := sigma_prime_pow_even p k hp hp2' hk4
  have hsig : (∑ d ∈ (p ^ k).divisors, d) = 2 * t := by omega
  have hcancel : 2 * m ^ 2 = 2 * (t * s) := by
    calc
      2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s := h1
      _ = (2 * t) * s := by rw [hsig]
      _ = 2 * (t * s) := by ring
  have hms : m ^ 2 = t * s := mul_left_cancel₀ two_ne_zero hcancel
  have hs_odd : Odd s := Nat.not_even_iff_odd.mp hs_not_even
  exact dris_packaged_absurd p k m s t s hp hm hpm hs_odd hsig hms h2
