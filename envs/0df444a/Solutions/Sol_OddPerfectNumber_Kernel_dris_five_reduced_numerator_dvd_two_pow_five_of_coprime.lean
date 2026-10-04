-- Prove2me | solution 1 for OddPerfectNumber.Kernel.dris_five_reduced_numerator_dvd_two_pow_five_of_coprime
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T15:02:07.924848+00:00
-- url     : https://prove2.me/submissions/2e4ce7a0-d12a-46c5-aba8-a42b865e4d1f

import Mathlib

/-- Counterexample: with `m = 0`, `(0 ^ 2).divisors = ∅`, so both divisor sums vanish.
Take `p = 2, m = 0, s = 0, u = 0, v = 0, w = 1`; every hypothesis holds
(`Nat.Coprime 0 1`), but `0 ∣ 2 * (2 ^ 5 * 1) = 64` is false. -/
theorem solution : ¬ (∀ (p m s u v w : Nat),
    Nat.Coprime u w →
    (∑ d ∈ (m ^ 2).divisors, d) = u * v →
    m ^ 2 = v * w →
    2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * s →
    (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * s →
    u ∣ 2 * (p ^ 5 * w)) := by
  intro h
  have h0 := h 2 0 0 0 0 1 (by decide) (by simp) (by simp) (by simp) (by simp)
  rw [zero_dvd_iff] at h0
  norm_num at h0
