-- Prove2me | solution 1 for TokenFinance.Debt.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:36:12.868878+00:00
-- url     : https://prove2.me/submissions/e7aa46d4-0edc-4fec-ab8b-d6dde69bd64c

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

theorem solution (c C0 θ : ℝ) (hc : 0 < c) (hcθ : c < θ) (hC0 : 0 < C0)
    (hnpv : 0 < npv c C0 θ) :
    0 < equityShare c C0 θ ∧ equityShare c C0 θ < 1 ∧
      equityShare c C0 θ = 12 * θ * C0 / (θ - c) ^ 3 ∧
      equityShare c C0 θ * expect θ (pim c) = C0 ∧
      (1 - equityShare c C0 θ) * expect θ (pim c) = npv c C0 θ := by
  have hθ : 0 < θ := by linarith
  have hL : 0 < θ - c := by linarith
  have hE : expect θ (pim c) = (θ - c) ^ 3 / (12 * θ) := TFDH.expect_pim c θ hc.le hcθ.le
  have hEpos : 0 < expect θ (pim c) := by rw [hE]; positivity
  have hnpv' : npv c C0 θ = expect θ (pim c) - C0 := rfl
  have hsh : equityShare c C0 θ = C0 / expect θ (pim c) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hsh]; positivity
  · rw [hsh, div_lt_one hEpos]; linarith
  · rw [hsh, hE]; field_simp
  · rw [hsh]; field_simp
  · rw [hsh, hnpv']; field_simp
