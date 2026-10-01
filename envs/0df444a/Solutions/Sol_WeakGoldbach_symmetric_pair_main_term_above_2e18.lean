-- Prove2me | solution 1 for WeakGoldbach.symmetric_pair_main_term_above_2e18
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @webmh
-- created : 2026-09-11T23:14:08.878459+00:00
-- url     : https://prove2.me/submissions/9a1d869e-c72a-4645-9bc0-3bce00fc5f87
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_symmetric_log_weighted_main_term_above_2e18
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

private lemma log_pair_product_le (x y c : ℝ)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hc : 1 ≤ c) (hxy : x + y = 2 * c) :
    Real.log x * Real.log y ≤ (Real.log c) ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hc0 : 0 < c := by linarith
  have hprod : x * y ≤ c ^ 2 := by nlinarith [sq_nonneg (x - y)]
  have hsum := Real.log_le_log (mul_pos hx0 hy0) hprod
  rw [Real.log_mul (ne_of_gt hx0) (ne_of_gt hy0), Real.log_pow] at hsum
  norm_num at hsum
  have hlogx := Real.log_nonneg hx
  have hlogy := Real.log_nonneg hy
  have hlogc := Real.log_nonneg hc
  have hsq := mul_nonneg (sub_nonneg.mpr hsum)
    (show 0 ≤ 2 * Real.log c + (Real.log x + Real.log y) by positivity)
  nlinarith [sq_nonneg (Real.log x - Real.log y)]

private lemma symmetric_weight_le_count (m : ℕ) (hm : 2 ≤ m) :
    (∑ t ∈ (Finset.range (m - 1)).filter
      (fun t => Nat.Prime (m - t) ∧ Nat.Prime (m + t)),
      Real.log (m - t : ℕ) * Real.log (m + t : ℕ)) ≤
    (((Finset.range (m - 1)).filter
      (fun t => Nat.Prime (m - t) ∧ Nat.Prime (m + t))).card : ℝ) *
      (Real.log m) ^ 2 := by
  classical
  calc
    _ ≤ ∑ t ∈ (Finset.range (m - 1)).filter
        (fun t => Nat.Prime (m - t) ∧ Nat.Prime (m + t)),
        (Real.log m) ^ 2 := by
      apply Finset.sum_le_sum
      intro t ht
      obtain ⟨ht, hp, hq⟩ := Finset.mem_filter.mp ht
      have ht' : t ≤ m := by have := Finset.mem_range.mp ht; omega
      apply log_pair_product_le
      · exact_mod_cast hp.one_lt.le
      · exact_mod_cast hq.one_lt.le
      · exact_mod_cast (show 1 ≤ m by omega)
      · push_cast
        rw [Nat.cast_sub ht']
        ring
    _ = _ := by simp

/-- Reduction to an OPEN logarithmically weighted binary Goldbach bound. -/
theorem solution (m : ℕ) (hm : 2 * 10 ^ 18 < m) :
    (∏ p ∈ (2 * m).primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2))
      * (m : ℝ) / (Real.log m) ^ 2
      ≤ ((Finset.range (m - 1)).filter
        (fun t => Nat.Prime (m - t) ∧ Nat.Prime (m + t))).card := by
  have hm2 : 2 ≤ m := by omega
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  apply (div_le_iff₀ (sq_pos_of_pos (Real.log_pos hm1))).2
  exact le_trans
    (WeakGoldbach.symmetric_log_weighted_main_term_above_2e18 m hm)
    (symmetric_weight_le_count m hm2)
