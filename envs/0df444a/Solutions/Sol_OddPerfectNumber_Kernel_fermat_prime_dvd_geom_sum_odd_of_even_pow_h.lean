-- Prove2me | solution 1 for OddPerfectNumber.Kernel.fermat_prime_dvd_geom_sum_odd_of_even_pow_h
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-30T17:06:35.312736+00:00
-- url     : https://prove2.me/submissions/0c4683a0-4fa0-4f19-89ba-952a9c5196ca

import Mathlib

theorem solution : ¬ (∀ (p t e : Nat), p.Prime →
    ¬ t ∣ p → (∃ k, p - 1 = 2 ^ k) →
    (∑ i ∈ Finset.range (2 * e + 1), t ^ i) ∣ p →
    (2 * e + 1) ∣ p) := by
  intro h
  have hh := h 3 0 2 (by norm_num) (by norm_num) ⟨1, by norm_num⟩ (by norm_num [Finset.sum_range_succ])
  norm_num at hh
