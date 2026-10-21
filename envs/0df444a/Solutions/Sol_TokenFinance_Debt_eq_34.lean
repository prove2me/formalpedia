-- Prove2me | solution 1 for TokenFinance.Debt.eq_34
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:38:31.115991+00:00
-- url     : https://prove2.me/submissions/576090b9-0d01-4e20-8641-629fa2ecb9c6

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

set_option autoImplicit false
open TokenFinance.Debt intervalIntegral

namespace TFDH

lemma cont_pim (c : ℝ) : Continuous (pim c) := by
  unfold pim; fun_prop

lemma cont_debtInv (c D : ℝ) : Continuous (debtInv c D) := by
  unfold debtInv; have := cont_pim c; fun_prop

lemma cont_debtEnt (c D : ℝ) : Continuous (debtEnt c D) := by
  unfold debtEnt; have := cont_pim c; fun_prop

lemma int_sq (c t : ℝ) : ∫ x in c..t, (x - c) ^ 2 / 4 = (t - c) ^ 3 / 12 := by
  rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_right (fun x => x ^ 2) c]
  simp [integral_pow]
  ring

lemma int_pim_zero (c : ℝ) (hc : 0 ≤ c) : ∫ x in (0:ℝ)..c, pim c x = 0 := by
  have : ∀ x ∈ Set.uIcc (0:ℝ) c, pim c x = 0 := by
    intro x hx
    rw [Set.uIcc_of_le hc] at hx
    unfold pim
    have : max (x - c) 0 = 0 := max_eq_right (by linarith [hx.2])
    rw [this]; norm_num
  rw [intervalIntegral.integral_congr this]; simp

lemma int_pim (c θ : ℝ) (hc : 0 ≤ c) (hcθ : c ≤ θ) : ∫ x in (0:ℝ)..θ, pim c x = (θ - c) ^ 3 / 12 := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := c) ((cont_pim c).intervalIntegrable _ _)
    ((cont_pim c).intervalIntegrable _ _), int_pim_zero c hc, zero_add]
  have : ∀ x ∈ Set.uIcc c θ, pim c x = (x - c) ^ 2 / 4 := by
    intro x hx
    rw [Set.uIcc_of_le hcθ] at hx
    unfold pim
    have : max (x - c) 0 = x - c := max_eq_left (by linarith [hx.1])
    rw [this]
  rw [intervalIntegral.integral_congr this, int_sq]

lemma expect_pim (c θ : ℝ) (hc : 0 ≤ c) (hcθ : c ≤ θ) : expect θ (pim c) = (θ - c) ^ 3 / (12 * θ) := by
  unfold expect
  rw [int_pim c θ hc hcθ]
  by_cases h : θ = 0
  · subst h; simp
  · field_simp

end TFDH

theorem solution (c C0 θ δ : ℝ) (hc : 0 < c) (hcθ : c < θ) (hC0 : 0 < C0)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (h33 : (θ - c) ^ 3 / (12 * θ) * (-2 * δ ^ 3 + 3 * δ ^ 2) - C0 = 0) :
    (θ - c) ^ 2 * δ ^ 2 / 4 = C0 * (θ / (θ - c)) * (3 / (3 - 2 * δ)) ∧
      C0 < (θ - c) ^ 2 * δ ^ 2 / 4 := by
  have hθ : 0 < θ := by linarith
  have hL : 0 < θ - c := by linarith
  have h3 : 0 < 3 - 2 * δ := by linarith
  have h3' : 3 - 2 * δ ≠ 0 := h3.ne'
  have h3'' : 3 - δ * 2 ≠ 0 := by intro h; linarith
  have hC : C0 = (θ - c) ^ 3 / (12 * θ) * (-2 * δ ^ 3 + 3 * δ ^ 2) := by linarith
  constructor
  · rw [hC, show (-2 * δ ^ 3 + 3 * δ ^ 2) = δ ^ 2 * (3 - 2 * δ) by ring]
    field_simp
    norm_num
  · rw [hC]
    have h1 : (θ - c) ^ 3 / (12 * θ) * (-2 * δ ^ 3 + 3 * δ ^ 2)
        = (θ - c) ^ 2 * δ ^ 2 / 4 * ((θ - c) * (3 - 2 * δ) / (3 * θ)) := by
      field_simp; ring
    rw [h1]
    have hpos : 0 < (θ - c) ^ 2 * δ ^ 2 / 4 := by positivity
    have hlt : (θ - c) * (3 - 2 * δ) / (3 * θ) < 1 := by
      rw [div_lt_one (by positivity)]
      nlinarith
    nlinarith
