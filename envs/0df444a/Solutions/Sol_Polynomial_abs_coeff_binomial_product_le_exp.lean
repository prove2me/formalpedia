-- Prove2me | solution 1 for Polynomial.abs_coeff_binomial_product_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:56:06.017314+00:00
-- url     : https://prove2.me/submissions/54b2314c-c0ab-40d9-ac0c-61e6e6684344

import Mathlib
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

namespace Polynomial

private theorem abs_coeff_binomial_product_weight_le_exp
    (q : ℝ) (hq : 0 ≤ q) (es : List ℕ) (n : ℕ) :
    |(((es.map fun e => (1 - X ^ e : ℤ[X])).prod).coeff n : ℝ)| * q ^ n ≤
      Real.exp ((es.map fun e => q ^ e).sum) := by
  induction es generalizing n with
  | nil =>
      by_cases hn : n = 0
      · simp [hn]
      · simp [coeff_one, hn]
  | cons e es ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [sub_mul, one_mul, coeff_sub, coeff_X_pow_mul']
      split_ifs with h
      · rw [Int.cast_sub]
        have hp : q ^ n = q ^ (n - e) * q ^ e := by
          rw [← pow_add, Nat.sub_add_cancel h]
        calc
          _ ≤ (|(((es.map fun j => (1 - X ^ j : ℤ[X])).prod).coeff n : ℝ)| +
              |(((es.map fun j => (1 - X ^ j : ℤ[X])).prod).coeff (n-e) : ℝ)|) * q ^ n :=
            mul_le_mul_of_nonneg_right (abs_sub _ _) (pow_nonneg hq n)
          _ = |(((es.map fun j => (1 - X ^ j : ℤ[X])).prod).coeff n : ℝ)| * q ^ n +
              (|(((es.map fun j => (1 - X ^ j : ℤ[X])).prod).coeff (n-e) : ℝ)| *
                q ^ (n-e)) * q ^ e := by rw [hp]; ring
          _ ≤ Real.exp ((es.map fun j => q ^ j).sum) +
              Real.exp ((es.map fun j => q ^ j).sum) * q ^ e :=
            add_le_add (ih n) (mul_le_mul_of_nonneg_right (ih (n-e)) (pow_nonneg hq e))
          _ = Real.exp ((es.map fun j => q ^ j).sum) * (1 + q ^ e) := by ring
          _ ≤ Real.exp ((es.map fun j => q ^ j).sum) * Real.exp (q ^ e) := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
            linarith [Real.add_one_le_exp (q ^ e)]
          _ = _ := by rw [← Real.exp_add]; congr 1; ring
      · simp only [sub_zero]
        exact (ih n).trans (Real.exp_le_exp.mpr (le_add_of_nonneg_left (pow_nonneg hq e)))

/-- An exponentially weighted coefficient bound for a monomial times a product of binomials. -/
theorem _root_.solution
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (es : List ℕ) (s n : ℕ) :
    |((X ^ s * (es.map fun e => (1 - X ^ e : ℤ[X])).prod).coeff n : ℝ)| * q ^ n ≤
      Real.exp ((es.map fun e => q ^ e).sum) := by
  rw [coeff_X_pow_mul']
  split_ifs with h
  · have hp : q ^ n = q ^ (n-s) * q ^ s := by
      rw [← pow_add, Nat.sub_add_cancel h]
    calc
      _ = (|(((es.map fun e => (1 - X ^ e : ℤ[X])).prod).coeff (n-s) : ℝ)| *
          q ^ (n-s)) * q ^ s := by rw [hp]; ring
      _ ≤ Real.exp ((es.map fun e => q ^ e).sum) * q ^ s :=
        mul_le_mul_of_nonneg_right
          (abs_coeff_binomial_product_weight_le_exp q hq₀ es (n-s)) (pow_nonneg hq₀ s)
      _ ≤ Real.exp ((es.map fun e => q ^ e).sum) := by
        exact mul_le_of_le_one_right (le_of_lt (Real.exp_pos _)) (pow_le_one₀ hq₀ hq₁)
  · simpa using (le_of_lt (Real.exp_pos ((es.map fun e => q ^ e).sum)))

end Polynomial
