-- Prove2me | solution 1 for RamanujanNotebooks.entry_5_25_i
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T14:26:11.548232+00:00
-- url     : https://prove2.me/submissions/aa7c3497-8959-418f-9850-752d974d611d

import Mathlib

namespace RNE5
open Real

theorem main (n : ℕ) (hn : 1 ≤ n) :
    HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ (2 * n))
      ((-1 : ℝ) ^ (n + 1) * (2 * Real.pi) ^ (2 * n) * ((bernoulli (2 * n) : ℚ) : ℝ)
        / (2 * ((2 * n).factorial : ℝ))) := by
  have h := hasSum_zeta_nat (k := n) (by omega)
  rw [← hasSum_nat_add_iff' 1] at h
  have h0 : (1 : ℝ) / ((0 : ℕ) : ℝ) ^ (2 * n) = 0 := by
    rw [Nat.cast_zero, zero_pow (by omega), div_zero]
  simp only [Finset.range_one, Finset.sum_singleton, h0, sub_zero, Nat.cast_add, Nat.cast_one] at h
  convert h using 1
  · rfl
  have h2 : (2 : ℝ) ^ (2 * n) = 2 * 2 ^ (2 * n - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [mul_pow, h2]
  field_simp

end RNE5

theorem solution (n : ℕ) (hn : 1 ≤ n) :
    HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ (2 * n))
      ((-1 : ℝ) ^ (n + 1) * (2 * Real.pi) ^ (2 * n) * ((bernoulli (2 * n) : ℚ) : ℝ)
        / (2 * ((2 * n).factorial : ℝ))) :=
  RNE5.main n hn
