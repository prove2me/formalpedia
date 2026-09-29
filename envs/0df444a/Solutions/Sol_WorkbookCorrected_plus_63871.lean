-- Prove2me | solution 1 for WorkbookCorrected.plus_63871
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T15:40:55.980307+00:00
-- url     : https://prove2.me/submissions/e75e497b-0181-4cbf-ae85-42b6de4dabe4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem solution (x : ℕ → ℝ) (x1 : x 1 = 1) (h : ∀ n : ℕ, 1 ≤ n → x (n+1)=Real.sqrt (1+(n:ℝ)*x n)) : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |x n / (n:ℝ)-1| < ε := by
  have hb : ∀ n : ℕ, 1 ≤ n → (n:ℝ)-2 ≤ x n ∧ x n ≤ (n:ℝ) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num [x1]
    | succ n hn ih =>
      have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
      have hx0 : 0 ≤ x n := by
        by_cases he : n=1
        · simpa [he,x1]
        · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n≠0 by omega)
          rw [h k (by omega)]
          exact Real.sqrt_nonneg _
      have hr : 0 ≤ 1+(n:ℝ)*x n := by positivity
      have hs := Real.sq_sqrt hr
      have hs0 := Real.sqrt_nonneg (1+(n:ℝ)*x n)
      rw [h n hn]
      push_cast
      constructor
      · nlinarith [mul_nonneg (show (0:ℝ) ≤ n by positivity) (sub_nonneg.mpr ih.1)]
      · nlinarith [mul_nonneg (show (0:ℝ) ≤ n by positivity) (sub_nonneg.mpr ih.2)]
  intro ε he
  obtain ⟨N,hN⟩ := exists_nat_gt (2/ε)
  refine ⟨max N 1,?_⟩
  intro n hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnR : (0:ℝ) < n := by exact_mod_cast hn1
  have hNr : (N:ℝ) ≤ n := by exact_mod_cast le_trans (le_max_left N 1) hn
  have hb' := hb n hn1
  have hh : 2/(n:ℝ) < ε := (div_lt_iff₀ hnR).2 (by have ht := (div_lt_iff₀ he).1 (lt_of_lt_of_le hN hNr); nlinarith)
  have hle : x n / (n:ℝ) ≤ 1 := (div_le_iff₀ hnR).2 (by simpa using hb'.2)
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  have hlow : 1-2/(n:ℝ) ≤ x n/(n:ℝ) := by
    apply (le_div_iff₀ hnR).2
    have hne : (n:ℝ) ≠ 0 := ne_of_gt hnR
    field_simp
    nlinarith [hb'.1]
  linarith
example : (∀ (x : ℕ → ℝ) (x1 : x 1 = 1) (h : ∀ n : ℕ, 1 ≤ n → x (n+1)=Real.sqrt (1+(n:ℝ)*x n)), ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |x n / (n:ℝ)-1| < ε) := @solution
#print axioms solution
