-- Prove2me | solution 1 for ZudilinZeta.zudilin_lemma1
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T12:12:52.361733+00:00
-- url     : https://prove2.me/submissions/ecd79814-4b91-45a3-a9d9-f0d94910a3c7

import Theorems.Thm_ZudilinZeta_zudilin_partial_fraction_data_exists
import Theorems.Thm_ZudilinZeta_zudilin_partial_fraction_integrality
import Theorems.Thm_ZudilinZeta_zudilin_partial_fraction_evaluation

set_option autoImplicit false
open ZudilinZeta

private lemma scale_eq_Lambda (P : Params) (n : ℕ) :
    (denominatorScale P n : ℝ) * F P n = Lambda P n := by
  simp only [denominatorScale, Lambda, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_prod]

theorem solution (P : Params) (n : ℕ) (hn : 0 < n) :
    (∃ c : ℕ → ℚ,
        F P n = (c 0 : ℝ)
          + ∑ k ∈ Finset.Icc 1 ((P.q - P.r - 2) / 2), (c k : ℝ) * zetaR (P.r + 2 * k)) ∧
      (∃ a : ℕ → ℤ,
        Lambda P n = (a 0 : ℝ)
          + ∑ k ∈ Finset.Icc 1 ((P.q - P.r - 2) / 2), (a k : ℝ) * zetaR (P.r + 2 * k)) := by
  classical
  obtain ⟨d⟩ := zudilin_partial_fraction_data_exists P n hn
  have he := zudilin_partial_fraction_evaluation P n d
  constructor
  · refine ⟨fun k => if k = 0 then d.constantCoefficient else d.zetaCoefficient (2*k+1), ?_⟩
    simp only [if_pos rfl]
    rw [he]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [if_neg (Nat.ne_of_gt (Finset.mem_Icc.mp hk).1)]
  · obtain ⟨⟨a0, ha0⟩, hint⟩ := zudilin_partial_fraction_integrality P n hn d
    have hall (k : ℕ) : ∃ a : ℤ, k ∈ Finset.Icc 1 ((P.q-P.r-2)/2) →
        denominatorScale P n * d.zetaCoefficient (2*k+1) = (a : ℚ) := by
      by_cases hk : k ∈ Finset.Icc 1 ((P.q-P.r-2)/2)
      · obtain ⟨a, ha⟩ := hint k hk
        exact ⟨a, fun _ => ha⟩
      · exact ⟨0, fun h => (hk h).elim⟩
    choose a ha using hall
    refine ⟨fun k => if k = 0 then a0 else a k, ?_⟩
    simp only [if_pos rfl]
    rw [← scale_eq_Lambda, he, mul_add, Finset.mul_sum]
    have h0 : (denominatorScale P n : ℝ) * (d.constantCoefficient : ℝ) = (a0 : ℝ) := by
      exact_mod_cast ha0
    rw [h0]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [if_neg (Nat.ne_of_gt (Finset.mem_Icc.mp hk).1), ← mul_assoc]
    have hk' : (denominatorScale P n : ℝ) * (d.zetaCoefficient (2*k+1) : ℝ) = (a k : ℝ) := by
      exact_mod_cast ha k hk
    rw [hk']
