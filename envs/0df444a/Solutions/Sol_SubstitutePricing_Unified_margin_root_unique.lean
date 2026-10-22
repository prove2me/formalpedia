-- Prove2me | solution 1 for SubstitutePricing.Unified.margin_root_unique
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:10:36.804129+00:00
-- url     : https://prove2.me/submissions/0c188ccc-96f5-41f9-8964-e87202eaa485

import Mathlib
import Definitions.Def_SubstitutePricing_Unified_Model
set_option autoImplicit false
open SubstitutePricing.Unified

theorem solution (M : Model) (hM : M.Assumptions) (σ : ℝ) (hσ : 0 < σ) :
    (∃! m : ℝ, M.marginLHS m = σ) ∧ ∀ m : ℝ, M.marginLHS m = σ → M.μ < m := by
  have hμ := hM.mu_pos
  have hgt : ∀ m : ℝ, M.marginLHS m = σ → M.μ < m := by
    intro m hm
    by_contra hle
    push_neg at hle
    have h1 : m / M.μ - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one hμ]; exact hle
    have h2 : M.marginLHS m ≤ 0 := by
      unfold Model.marginLHS
      exact mul_nonpos_of_nonpos_of_nonneg h1 (Real.exp_pos _).le
    linarith
  refine ⟨?_, hgt⟩
  have hcont : Continuous (fun m : ℝ => M.marginLHS m) := by
    unfold Model.marginLHS
    fun_prop
  set K := σ + |M.u0| / M.μ with hK
  have hK0 : 0 < K := by positivity
  obtain ⟨m, -, hm⟩ : σ ∈ (fun m : ℝ => M.marginLHS m) '' Set.Icc M.μ (M.μ * (1 + K)) := by
    have hle : M.μ ≤ M.μ * (1 + K) := by nlinarith
    apply intermediate_value_Icc hle hcont.continuousOn
    constructor
    · have : M.marginLHS M.μ = 0 := by
        unfold Model.marginLHS
        rw [div_self hμ.ne']; simp
      rw [this]; exact hσ.le
    · have e1 : M.μ * (1 + K) / M.μ - 1 = K := by field_simp; ring
      have hu : 0 ≤ 1 + K + M.u0 / M.μ := by
        have : -( |M.u0| / M.μ) ≤ M.u0 / M.μ := by
          rw [← neg_div]
          exact div_le_div_of_nonneg_right (neg_abs_le _) hμ.le
        rw [hK]; linarith
      have e2 : (M.μ * (1 + K) + M.u0) / M.μ = 1 + K + M.u0 / M.μ := by field_simp
      have h3 : 1 ≤ Real.exp ((M.μ * (1 + K) + M.u0) / M.μ) := by
        rw [e2]; exact Real.one_le_exp hu
      unfold Model.marginLHS
      rw [e1]
      have hKσ : σ ≤ K := by rw [hK]; have : 0 ≤ |M.u0| / M.μ := by positivity
                             linarith
      nlinarith
  refine ⟨m, hm, ?_⟩
  intro y hy
  have hmy := hgt y hy
  have hmm := hgt m hm
  -- strict monotonicity on (μ, ∞)
  have mono : ∀ a b : ℝ, M.μ < a → a < b → M.marginLHS a < M.marginLHS b := by
    intro a b ha hab
    unfold Model.marginLHS
    have h1 : 0 < a / M.μ - 1 := by
      rw [sub_pos, one_lt_div hμ]; exact ha
    have h2 : a / M.μ - 1 < b / M.μ - 1 := by
      have : a / M.μ < b / M.μ := div_lt_div_of_pos_right hab hμ
      linarith
    have h3 : Real.exp ((a + M.u0) / M.μ) ≤ Real.exp ((b + M.u0) / M.μ) := by
      apply Real.exp_le_exp.2
      exact div_le_div_of_nonneg_right (by linarith) hμ.le
    have h4 := Real.exp_pos ((a + M.u0) / M.μ)
    calc (a / M.μ - 1) * Real.exp ((a + M.u0) / M.μ)
        < (b / M.μ - 1) * Real.exp ((a + M.u0) / M.μ) := mul_lt_mul_of_pos_right h2 h4
      _ ≤ (b / M.μ - 1) * Real.exp ((b + M.u0) / M.μ) :=
          mul_le_mul_of_nonneg_left h3 (by linarith)
  rcases lt_trichotomy y m with h | h | h
  · have := mono y m hmy h; linarith
  · exact h
  · have := mono m y hmm h; linarith
