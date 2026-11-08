-- Prove2me | solution 1 for UltrametricFit.gamma_le
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:37:38.248272+00:00
-- url     : https://prove2.me/submissions/ed18e964-75e1-4424-b2db-39df1046c377

import Mathlib
import Definitions.Def_UltrametricFit_errLayer

open UltrametricFit in
theorem solution (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, 1 ≤ p → 0 < Gamma δ p ∧ Gamma δ p ≤ C * p := by
  have h12 : 0 < 1 - 2 * δ := by linarith
  have hG0 : 0 < Gamma0 δ := by
    unfold Gamma0
    have : 0 < (1 - δ) / (δ * (1 - 2 * δ) ^ 2) := by
      apply div_pos (by linarith); positivity
    linarith
  have hc : 1 < (Gamma0 δ + 1) / Gamma0 δ := by
    rw [lt_div_iff₀ hG0]; linarith
  have hcpos : 0 < (Gamma0 δ + 1) / Gamma0 δ := by linarith
  have hL : 0 < Real.log ((Gamma0 δ + 1) / Gamma0 δ) := Real.log_pos hc
  refine ⟨2 / Real.log ((Gamma0 δ + 1) / Gamma0 δ), div_pos two_pos hL, fun p hp => ?_⟩
  have hp0 : 0 < p := by linarith
  have hLp : 0 < Real.log ((Gamma0 δ + 1) / Gamma0 δ) / p := div_pos hL hp0
  have hexp : Real.log ((Gamma0 δ + 1) / Gamma0 δ) / p ≤
      ((Gamma0 δ + 1) / Gamma0 δ) ^ (1 / p) - 1 := by
    rw [Real.rpow_def_of_pos hcpos]
    have := Real.add_one_le_exp (Real.log ((Gamma0 δ + 1) / Gamma0 δ) * (1 / p))
    have e : Real.log ((Gamma0 δ + 1) / Gamma0 δ) * (1 / p)
        = Real.log ((Gamma0 δ + 1) / Gamma0 δ) / p := by ring
    rw [e] at this ⊢
    linarith
  have hden : 0 < ((Gamma0 δ + 1) / Gamma0 δ) ^ (1 / p) - 1 := lt_of_lt_of_le hLp hexp
  unfold Gamma
  refine ⟨div_pos two_pos hden, ?_⟩
  calc 2 / (((Gamma0 δ + 1) / Gamma0 δ) ^ (1 / p) - 1)
      ≤ 2 / (Real.log ((Gamma0 δ + 1) / Gamma0 δ) / p) :=
        div_le_div_of_nonneg_left (by norm_num) hLp hexp
    _ = 2 / Real.log ((Gamma0 δ + 1) / Gamma0 δ) * p := by
        field_simp
