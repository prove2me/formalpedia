-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.changed_factors_product_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:15:38.825079+00:00
-- url     : https://prove2.me/submissions/87e99700-5775-49d4-b833-8b4837460e4f

import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators

theorem solution {I : Type*} [DecidableEq I] (T E : Finset I) (x y : I → ℝ) (C : ℝ)
    (hx : ∀ i ∈ T, 0 ≤ x i)
    (hchanged : ∀ i ∈ T, i ∈ E → x i ≤ C * y i)
    (hunchanged : ∀ i ∈ T, i ∉ E → x i = y i) :
    (∏ i ∈ T, x i) ≤ C ^ (T.filter (· ∈ E)).card * ∏ i ∈ T, y i := by
  classical
  calc
    (∏ i ∈ T, x i) ≤ ∏ i ∈ T, ((if i ∈ E then C else 1) * y i) := by
      apply Finset.prod_le_prod hx
      intro i hi
      by_cases he : i ∈ E
      · simpa [he] using hchanged i hi he
      · simp [he, hunchanged i hi he]
    _ = (∏ i ∈ T, (if i ∈ E then C else 1)) * (∏ i ∈ T, y i) := by
      rw [Finset.prod_mul_distrib]
    _ = C ^ (T.filter (· ∈ E)).card * ∏ i ∈ T, y i := by simp [Finset.filter_mem_eq_inter]
