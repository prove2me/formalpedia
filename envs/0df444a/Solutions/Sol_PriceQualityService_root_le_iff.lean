-- Prove2me | solution 1 for PriceQualityService.root_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:12:48.215959+00:00
-- url     : https://prove2.me/submissions/37a960d2-cd4a-448d-a53e-df9436eb2afe

import Mathlib

theorem solution {N : ℕ} (w w' : Fin N → ℝ) (r r' : ℝ)
    (hr : r = ∑ i, Real.exp (w i - r - 1)) (hr' : r' = ∑ i, Real.exp (w' i - r' - 1)) :
    r ≤ r' ↔ ∑ i, Real.exp (w i) ≤ ∑ i, Real.exp (w' i) := by
  have hr0 : 0 ≤ r := by
    rw [hr]; exact Finset.sum_nonneg (fun i _ => (Real.exp_pos _).le)
  have hr0' : 0 ≤ r' := by
    rw [hr']; exact Finset.sum_nonneg (fun i _ => (Real.exp_pos _).le)
  have hA : r * Real.exp (r + 1) = ∑ i, Real.exp (w i) := by
    calc r * Real.exp (r + 1) = (∑ i, Real.exp (w i - r - 1)) * Real.exp (r + 1) := by
          nth_rewrite 1 [hr]; rfl
      _ = ∑ i, Real.exp (w i - r - 1) * Real.exp (r + 1) := Finset.sum_mul _ _ _
      _ = ∑ i, Real.exp (w i) := Finset.sum_congr rfl (fun i _ => by
          rw [← Real.exp_add]; congr 1; ring)
  have hA' : r' * Real.exp (r' + 1) = ∑ i, Real.exp (w' i) := by
    calc r' * Real.exp (r' + 1) = (∑ i, Real.exp (w' i - r' - 1)) * Real.exp (r' + 1) := by
          nth_rewrite 1 [hr']; rfl
      _ = ∑ i, Real.exp (w' i - r' - 1) * Real.exp (r' + 1) := Finset.sum_mul _ _ _
      _ = ∑ i, Real.exp (w' i) := Finset.sum_congr rfl (fun i _ => by
          rw [← Real.exp_add]; congr 1; ring)
  constructor
  · intro h
    rw [← hA, ← hA']
    exact mul_le_mul h (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le hr0'
  · intro h
    by_contra hlt
    push_neg at hlt
    have h1 : r' * Real.exp (r' + 1) ≤ r' * Real.exp (r + 1) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hr0'
    have h2 : r' * Real.exp (r + 1) < r * Real.exp (r + 1) :=
      mul_lt_mul_of_pos_right hlt (Real.exp_pos _)
    linarith
