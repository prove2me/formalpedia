-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.harmonic_gap_ge_removed_fraction
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:54:50.567283+00:00
-- url     : https://prove2.me/submissions/3efd962b-8ad2-4fad-b9e7-25cb54e40635

import Mathlib
noncomputable section
open scoped Classical BigOperators

theorem solution (m n : ℕ) (hmn : m ≤ n) :
    ((n - m : ℕ) : ℝ) / n ≤ (harmonic n : ℝ) - harmonic m := by
  induction n with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    simp
  | succ n ih =>
    by_cases hm : m = n+1
    · subst m
      simp
    · have hmn' : m ≤ n := by omega
      have hi := ih hmn'
      by_cases hn : n = 0
      · subst n
        have hm0 : m = 0 := by omega
        subst m
        norm_num [harmonic_succ]
      · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
        have hn1 : (0 : ℝ) < n+1 := by positivity
        have hdiff : ((n+1-m : ℕ) : ℝ) = ((n-m : ℕ) : ℝ) + 1 := by
          have hh : n+1-m = (n-m)+1 := by omega
          exact_mod_cast hh
        have hnon : (0 : ℝ) ≤ (n-m : ℕ) := by positivity
        have hfrac : ((n-m : ℕ) : ℝ)/(n+1) ≤ ((n-m : ℕ) : ℝ)/n := by
          apply div_le_div_of_nonneg_left hnon hnpos (by linarith)
        have hcast : (harmonic (n+1) : ℝ) = (harmonic n : ℝ) + 1 / (n+1) := by
          rw [harmonic_succ]
          norm_num [div_eq_mul_inv]
        rw [hdiff,hcast]
        push_cast
        rw [add_div]
        linarith
