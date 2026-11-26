-- Prove2me | solution 1 for OddPerfectNumber.nielsen_calibration_prod
-- status  : ACCEPTED   (prove)
-- author  : @curiyu
-- created : 2026-09-08T04:11:43.006618+00:00
-- url     : https://prove2.me/submissions/f8f9fc81-1ef9-4af6-86b3-f8427cd5a478

import Mathlib

open BigOperators Finset

private theorem key_nat (a m : ℕ) :
    (a + 1) ^ (2 ^ m) = a * ∏ i ∈ Finset.range m, ((a + 1) ^ (2 ^ i) + 1) + 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ]
    have h2 : 2 ^ (m + 1) = 2 ^ m * 2 := by ring
    rw [h2, pow_mul, ih]
    ring

private theorem sum_two_pow (m : ℕ) : ∑ i ∈ Finset.range m, 2 ^ i = 2 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have h2 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
    have hpos : 0 < 2 ^ m := by positivity
    omega

theorem solution (a r : ℕ) (ha : 0 < a) (hr : 0 < r) :
    (∏ i ∈ Finset.range (r - 1), (1 - 1 / (((a + 1) ^ (2 ^ i) + 1 : ℕ) : ℚ))) *
      (1 - 1 / ((((a + 1) ^ (2 ^ (r - 1)) : ℕ)) : ℚ)) =
      ((a : ℕ) : ℚ) / (((a : ℕ) : ℚ) + 1) := by
  have hfactor : ∀ X : ℚ, X ≠ 0 → 1 - 1 / X = (X - 1) / X := by
    intro X hX; field_simp
  have hXi : ∀ i ∈ Finset.range (r - 1),
      ((((a + 1) ^ (2 ^ i) + 1 : ℕ)) : ℚ) ≠ 0 := by
    intro i _
    positivity
  have hXlast : ((((a + 1) ^ (2 ^ (r - 1)) : ℕ)) : ℚ) ≠ 0 := by
    positivity
  have hprod : (∏ i ∈ Finset.range (r - 1),
      (1 - 1 / ((((a + 1) ^ (2 ^ i) + 1 : ℕ)) : ℚ))) =
      ∏ i ∈ Finset.range (r - 1),
        (((((a + 1) ^ (2 ^ i) + 1 : ℕ)) : ℚ) - 1) / ((((a + 1) ^ (2 ^ i) + 1 : ℕ)) : ℚ) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact hfactor _ (hXi i hi)
  rw [hprod, Finset.prod_div_distrib, hfactor _ hXlast]
  have hnum : ∀ i : ℕ,
      (((((a + 1) ^ (2 ^ i) + 1 : ℕ)) : ℚ) - 1) = ((((a + 1) ^ (2 ^ i) : ℕ)) : ℚ) := by
    intro i
    rw [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  have hnumprod : (∏ i ∈ Finset.range (r - 1),
      (((((a + 1) ^ (2 ^ i) + 1 : ℕ)) : ℚ) - 1)) =
      ∏ i ∈ Finset.range (r - 1), ((((a + 1) ^ (2 ^ i) : ℕ)) : ℚ) := by
    apply Finset.prod_congr rfl
    intro i _
    exact hnum i
  rw [hnumprod]
  have key := key_nat a (r - 1)
  have hsum := sum_two_pow (r - 1)
  have hP : (∏ i ∈ Finset.range (r - 1), (a + 1) ^ (2 ^ i)) = (a + 1) ^ (2 ^ (r - 1) - 1) := by
    rw [Finset.prod_pow_eq_pow_sum, hsum]
  have hA : (a + 1) ^ (2 ^ (r - 1)) = (a + 1) * (a + 1) ^ (2 ^ (r - 1) - 1) := by
    have hpos2 : 0 < 2 ^ (r - 1) := by positivity
    have hexp : 2 ^ (r - 1) = (2 ^ (r - 1) - 1) + 1 := by omega
    conv_lhs => rw [hexp, pow_succ]
    ring
  have keyQ : ((((a + 1) ^ (2 ^ (r - 1)) : ℕ)) : ℚ)
      = ((a : ℕ) : ℚ) * ((((∏ i ∈ Finset.range (r - 1), ((a + 1) ^ (2 ^ i) + 1) : ℕ))) : ℚ) + 1 := by
    exact_mod_cast key
  have hPQ : (∏ i ∈ Finset.range (r - 1), ((((a + 1) ^ (2 ^ i) + 1 : ℕ)) : ℚ))
      = ((((∏ i ∈ Finset.range (r - 1), ((a + 1) ^ (2 ^ i) + 1) : ℕ))) : ℚ) := by
    rw [Nat.cast_prod]
  have hPn : (∏ i ∈ Finset.range (r - 1), ((((a + 1) ^ (2 ^ i) : ℕ)) : ℚ))
      = ((((a + 1) ^ (2 ^ (r - 1) - 1) : ℕ)) : ℚ) := by
    rw [← Nat.cast_prod, ← hP]
  have hAQ : ((((a + 1) ^ (2 ^ (r - 1)) : ℕ)) : ℚ)
      = ((((a + 1 : ℕ))) : ℚ) * ((((a + 1) ^ (2 ^ (r - 1) - 1) : ℕ)) : ℚ) := by
    exact_mod_cast hA
  have hAcast : ((((a + 1 : ℕ))) : ℚ) = ((a : ℕ) : ℚ) + 1 := by
    rw [Nat.cast_add, Nat.cast_one]
  have hQne : ((((∏ i ∈ Finset.range (r - 1), ((a + 1) ^ (2 ^ i) + 1) : ℕ))) : ℚ) ≠ 0 := by
    positivity
  have hPne : ((((a + 1) ^ (2 ^ (r - 1) - 1) : ℕ)) : ℚ) ≠ 0 := by
    positivity
  have hane : ((a : ℕ) : ℚ) + 1 ≠ 0 := by positivity
  have hT : ((((a + 1 : ℕ))) : ℚ) * ((((a + 1) ^ (2 ^ (r - 1) - 1) : ℕ)) : ℚ)
      = ((a : ℕ) : ℚ) * ((((∏ i ∈ Finset.range (r - 1), ((a + 1) ^ (2 ^ i) + 1) : ℕ))) : ℚ) + 1 := by
    rw [← hAQ]; exact keyQ
  rw [hPQ, hPn, hAQ, hT, add_sub_cancel_right, ← hT, div_mul_div_comm, hAcast]
  have hAPne : (((a : ℕ) : ℚ) + 1) * ((((a + 1) ^ (2 ^ (r - 1) - 1) : ℕ)) : ℚ) ≠ 0 :=
    mul_ne_zero hane hPne
  field_simp
