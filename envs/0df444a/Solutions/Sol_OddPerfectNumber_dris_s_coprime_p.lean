-- Prove2me | solution 1 for OddPerfectNumber.dris_s_coprime_p
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T08:40:23.618672+00:00
-- url     : https://prove2.me/submissions/8fbc74b9-8146-4501-a54d-a11ecd449b5f

import Mathlib

theorem solution (p k m s : Nat) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpm : ¬ p ∣ m)
    (h : 2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s) : ¬ p ∣ s := by
  intro hps
  have hsdvd : s ∣ 2 * m ^ 2 :=
    by
    have h1 : s ∣ (∑ d ∈ (p ^ k).divisors, d) * s := dvd_mul_left _ _
    rwa [← h] at h1
  have h1 : p ∣ 2 * m ^ 2 := dvd_trans hps hsdvd
  rcases (hp.prime.dvd_mul).mp h1 with h2 | hm2
  · have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    have hge := hp.two_le
    omega
  · exact hpm (hp.prime.dvd_of_dvd_pow hm2)
