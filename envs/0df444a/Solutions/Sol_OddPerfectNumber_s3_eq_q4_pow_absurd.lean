-- Prove2me | solution 1 for OddPerfectNumber.s3_eq_q4_pow_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T21:12:03.32136+00:00
-- url     : https://prove2.me/submissions/c08d1b36-6a46-48c9-b731-14153ed3e8fb

import Mathlib

theorem solution (q4 t beta : Nat)
    (hbeta : 0 < beta)
    (hgt : q4 < ∑ i ∈ Finset.range t, 3 ^ i)
    (hndvd : ¬ q4 ^ 2 ∣ ∑ i ∈ Finset.range t, 3 ^ i)
    (hpow : ∑ i ∈ Finset.range t, 3 ^ i = q4 ^ beta) :
    False := by
  have hb1 : beta = 1 := by
    rcases lt_or_eq_of_le (Nat.one_le_iff_ne_zero.mpr hbeta.ne') with h2 | h1
    · exfalso
      have hdvd2 : q4 ^ 2 ∣ q4 ^ beta := pow_dvd_pow q4 (by omega)
      rw [← hpow] at hdvd2
      exact hndvd hdvd2
    · exact h1.symm
  have hS : ∑ i ∈ Finset.range t, 3 ^ i = q4 := by
    rw [hpow, hb1, pow_one]
  omega
