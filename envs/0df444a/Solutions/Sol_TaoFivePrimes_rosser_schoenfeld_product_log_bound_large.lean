-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_product_log_bound_large
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T12:15:35.879771+00:00
-- url     : https://prove2.me/submissions/2e2f528c-0752-49c6-bd4f-b90c4e2aa5a3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TaoFivePrimes_reciprocal_prime_sum_upper_bound_strict
import Theorems.Thm_TaoFivePrimes_mertens_tail_le_partial_sum
import Mathlib

open TaoFivePrimes

theorem solution (x : ℝ) (hx : 10 ^ 8 ≤ x) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log ((p : ℝ) / ((p : ℝ) - 1)) <
      Real.eulerMascheroniConstant + Real.log (Real.log x) +
        Real.log (1 + 1 / (2 * (Real.log x) ^ 2)) := by
  have hterm (p : ℕ) (hp : p ∈ Nat.primesLE ⌊x⌋₊) :
      Real.log ((p : ℝ) / ((p : ℝ) - 1)) =
        1 / (p : ℝ) - (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)) := by
    have hprime : p.Prime := (Nat.mem_primesLE.mp hp).2
    have hpone : 1 < p := hprime.one_lt
    have hq : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpone
    have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (by linarith)
    have hpm1 : (p : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
    have hr : (p : ℝ) / ((p : ℝ) - 1) = (1 - 1 / (p : ℝ))⁻¹ := by
      field_simp [hp0, hpm1]
      <;> ring
    rw [hr, Real.log_inv]
    ring
  have hidentity :
      (∑ p ∈ Nat.primesLE ⌊x⌋₊,
        Real.log ((p : ℝ) / ((p : ℝ) - 1))) =
        (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) -
          ∑ p ∈ Nat.primesLE ⌊x⌋₊,
            (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    exact hterm p hp
  have hrec := reciprocal_prime_sum_upper_bound_strict x hx
  have htail := mertens_tail_le_partial_sum x
  rw [hidentity]
  linarith
