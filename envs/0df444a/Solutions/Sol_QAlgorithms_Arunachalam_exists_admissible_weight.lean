-- Prove2me | solution 1 for QAlgorithms.Arunachalam.exists_admissible_weight
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T00:07:58.207062+00:00
-- url     : https://prove2.me/submissions/94892a6a-3596-4b7f-9f65-0cf2c1d123cf

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false

private lemma log_weight_bounds (N M : ℕ) (hN : 1 ≤ N) (hNM : N < M)
    (hM : M ≤ 2 ^ N) :
    0 < Real.logb 2 (M : ℝ) ∧ Real.logb 2 (M : ℝ) ≤ N := by
  have hM1 : (1 : ℝ) < M := by exact_mod_cast (lt_of_le_of_lt hN hNM)
  constructor
  · exact Real.logb_pos (by norm_num) hM1
  · have h := Real.logb_le_logb_of_le (b := 2) (by norm_num)
      (by positivity : (0 : ℝ) < M) (by exact_mod_cast hM : (M : ℝ) ≤ (2 : ℝ) ^ N)
    simpa [Real.logb_pow, Real.logb_self_eq_one] using h

theorem solution :
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ N M : ℕ, 1 ≤ N → N < M → M ≤ 2 ^ N →
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ N ∧
        c0 * (Real.logb 2 (M : ℝ) / (Real.logb 2 ((N : ℝ) / Real.logb 2 (M : ℝ)) + 1)) ≤ (k : ℝ) ∧
        N.choose (k - 1) + N.choose k ≤ M := by
  refine ⟨1, by norm_num, ?_⟩
  intro N M hN hNM hM
  obtain ⟨hLpos, hLN⟩ := log_weight_bounds N M hN hNM hM
  have hratio : (1 : ℝ) ≤ (N : ℝ) / Real.logb 2 (M : ℝ) :=
    (le_div_iff₀ hLpos).2 (by simpa [Real.logb_pow, Real.logb_self_eq_one] using hLN)
  have hlog : 0 ≤ Real.logb 2 ((N : ℝ) / Real.logb 2 (M : ℝ)) :=
    Real.logb_nonneg (by norm_num) hratio
  refine ⟨N, hN, le_rfl, ?_, ?_⟩
  · have hden : 0 < Real.logb 2 ((N : ℝ) / Real.logb 2 (M : ℝ)) + 1 := by linarith
    rw [one_mul, div_le_iff₀ hden]
    nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  · rw [Nat.choose_symm hN, Nat.choose_one_right, Nat.choose_self]
    omega
