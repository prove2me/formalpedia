-- Prove2me | solution 1 for TokenFinance.Debt.eq_8
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:42:22.965752+00:00
-- url     : https://prove2.me/submissions/8ae0f2a9-7d49-4cf4-b352-aa13adbfb3d4

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

theorem solution (c C0 θ D : ℝ) (hc : 0 < c) (hcθ : c < θ) (hD : 0 ≤ D)
    (h7 : expect θ (debtInv c D) = C0) :
    expect θ (debtEnt c D) = npv c C0 θ ∧
      (c + 2 * Real.sqrt D ≤ θ →
        expect θ (debtEnt c D) = ∫ x in (c + 2 * Real.sqrt D)..θ, 1 / θ * ((x - c) ^ 2 / 4 - D)) := by
  have hθ : 0 < θ := by linarith
  have hpt : ∀ x, debtInv c D x + debtEnt c D x = pim c x := by
    intro x
    unfold debtInv debtEnt
    rcases le_total (pim c x) D with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
  constructor
  · have h1 : ∫ x in (0:ℝ)..θ, debtEnt c D x
        = (∫ x in (0:ℝ)..θ, pim c x) - ∫ x in (0:ℝ)..θ, debtInv c D x := by
      rw [← intervalIntegral.integral_sub ((TFDH.cont_pim c).intervalIntegrable _ _)
        ((TFDH.cont_debtInv c D).intervalIntegrable _ _)]
      apply intervalIntegral.integral_congr
      intro x _
      have := hpt x
      simp only
      linarith
    have : expect θ (debtEnt c D) = expect θ (pim c) - expect θ (debtInv c D) := by
      unfold expect
      rw [h1, sub_div]
    rw [this, h7]
    rfl
  · intro hm
    set m : ℝ := c + 2 * Real.sqrt D with hmdef
    have hs0 : 0 ≤ Real.sqrt D := Real.sqrt_nonneg D
    have hsq : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD
    have hm0 : 0 ≤ m := by rw [hmdef]; linarith
    have hz : ∫ x in (0:ℝ)..m, debtEnt c D x = 0 := by
      have : ∀ x ∈ Set.uIcc (0:ℝ) m, debtEnt c D x = 0 := by
        intro x hx
        rw [Set.uIcc_of_le hm0] at hx
        unfold debtEnt pim
        have h1 : max (x - c) 0 ≤ 2 * Real.sqrt D := by
          apply max_le
          · rw [hmdef] at hx; linarith [hx.2]
          · linarith
        have h2 : (max (x - c) 0) ^ 2 ≤ (2 * Real.sqrt D) ^ 2 := by
          have : 0 ≤ max (x - c) 0 := le_max_right _ _
          exact pow_le_pow_left₀ this h1 2
        have h3 : (2 * Real.sqrt D) ^ 2 = 4 * D := by rw [mul_pow, hsq]; norm_num
        apply max_eq_right
        linarith
      rw [intervalIntegral.integral_congr this]; simp
    have hr : ∫ x in m..θ, debtEnt c D x = ∫ x in m..θ, ((x - c) ^ 2 / 4 - D) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hm] at hx
      have hxc : c ≤ x := by rw [hmdef] at hx; linarith [hx.1]
      have h1 : 2 * Real.sqrt D ≤ x - c := by rw [hmdef] at hx; linarith [hx.1]
      have h2 : (2 * Real.sqrt D) ^ 2 ≤ (x - c) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
      have h3 : (2 * Real.sqrt D) ^ 2 = 4 * D := by rw [mul_pow, hsq]; norm_num
      have hmx : max (x - c) 0 = x - c := max_eq_left (by linarith)
      show max (pim c x - D) 0 = (x - c) ^ 2 / 4 - D
      unfold pim
      rw [hmx]
      exact max_eq_left (by linarith)
    have : expect θ (debtEnt c D) = (∫ x in m..θ, ((x - c) ^ 2 / 4 - D)) / θ := by
      unfold expect
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := m)
        ((TFDH.cont_debtEnt c D).intervalIntegrable _ _) ((TFDH.cont_debtEnt c D).intervalIntegrable _ _), hz, hr, zero_add]
    rw [this, intervalIntegral.integral_const_mul]
    field_simp
