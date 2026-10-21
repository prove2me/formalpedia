-- Prove2me | solution 1 for PriceQualityService.Uniform.equation_25
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:28:43.712298+00:00
-- url     : https://prove2.me/submissions/76afe13c-e0ba-4526-9d44-b5a0bf6c170a

import Mathlib
import Definitions.Def_PriceQualityService_Uniform_Reduction

set_option autoImplicit false
open PriceQualityService.Uniform Finset

theorem gTerm_eq' {N : ℕ} (α a b c s : Fin N → ℝ) (r t : ℝ) (i : Fin N) :
    gTerm α a b c s r t i = Real.exp (exponent α a b c s t i) / Real.exp (1 + r) := by
  unfold gTerm
  rw [← Real.exp_sub]; congr 1; ring

theorem sum_gTerm' {N : ℕ} (α a b c s : Fin N → ℝ) (r t : ℝ) :
    ∑ i, gTerm α a b c s r t i = yTotal α a b c s t / Real.exp (1 + r) := by
  simp_rw [gTerm_eq']
  rw [← Finset.sum_div]; rfl

theorem yTotal_nonneg' {N : ℕ} (α a b c s : Fin N → ℝ) (t : ℝ) : 0 ≤ yTotal α a b c s t :=
  Finset.sum_nonneg (fun i _ => (Real.exp_pos _).le)

theorem solution {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) :
    (∀ r t : ℝ, r = ∑ i, gTerm α a b c s r t i ↔ r = yTotal α a b c s t / Real.exp (1 + r)) ∧
    ∀ R : ℝ → ℝ, (∀ t, R t = ∑ i, gTerm α a b c s (R t) t i) →
      ∀ t t' : ℝ, yTotal α a b c s t ≤ yTotal α a b c s t' → R t ≤ R t' := by
  refine ⟨fun r t => by rw [sum_gTerm'], ?_⟩
  intro R hR t t' hyt
  have h1 : R t = yTotal α a b c s t / Real.exp (1 + R t) := by
    rw [← sum_gTerm']; exact hR t
  have h2 : R t' = yTotal α a b c s t' / Real.exp (1 + R t') := by
    rw [← sum_gTerm']; exact hR t'
  by_contra hlt
  push_neg at hlt
  have hexp : Real.exp (1 + R t') ≤ Real.exp (1 + R t) := Real.exp_le_exp.mpr (by linarith)
  have hp' : 0 < Real.exp (1 + R t') := Real.exp_pos _
  have hp : 0 < Real.exp (1 + R t) := Real.exp_pos _
  have : R t ≤ R t' := by
    rw [h1, h2]
    calc yTotal α a b c s t / Real.exp (1 + R t)
        ≤ yTotal α a b c s t' / Real.exp (1 + R t) := by
          exact div_le_div_of_nonneg_right hyt hp.le
      _ ≤ yTotal α a b c s t' / Real.exp (1 + R t') := by
          exact div_le_div_of_nonneg_left (yTotal_nonneg' α a b c s t') hp' hexp
  linarith
