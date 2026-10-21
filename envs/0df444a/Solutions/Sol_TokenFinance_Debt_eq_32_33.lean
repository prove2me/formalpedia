-- Prove2me | solution 1 for TokenFinance.Debt.eq_32_33
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:43:57.984007+00:00
-- url     : https://prove2.me/submissions/53896818-e0b8-4e72-b072-fcbaa47a5ffa

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

theorem solution (c C0 θ δ : ℝ) (hc : 0 < c) (hcθ : c < θ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    expect θ (debtInv c ((θ - c) ^ 2 * δ ^ 2 / 4)) - C0 =
        (∫ x in c..(c + δ * (θ - c)), 1 / θ * ((x - c) ^ 2 / 4)) +
          (∫ _x in (c + δ * (θ - c))..θ, 1 / θ * ((θ - c) ^ 2 * δ ^ 2 / 4)) - C0 ∧
      expect θ (debtInv c ((θ - c) ^ 2 * δ ^ 2 / 4)) - C0 =
        (θ - c) ^ 3 / (12 * θ) * (-2 * δ ^ 3 + 3 * δ ^ 2) - C0 := by
  have hθ : 0 < θ := by linarith
  have hL : 0 < θ - c := by linarith
  set L : ℝ := θ - c with hLdef
  set D : ℝ := L ^ 2 * δ ^ 2 / 4 with hDdef
  set m : ℝ := c + δ * L with hmdef
  have hm1 : c ≤ m := by rw [hmdef]; nlinarith
  have hm2 : m ≤ θ := by rw [hmdef]; nlinarith
  have hz : ∫ x in (0:ℝ)..c, debtInv c D x = 0 := by
    have : ∀ x ∈ Set.uIcc (0:ℝ) c, debtInv c D x = 0 := by
      intro x hx
      rw [Set.uIcc_of_le hc.le] at hx
      unfold debtInv pim
      have : max (x - c) 0 = 0 := max_eq_right (by linarith [hx.2])
      rw [this]
      have : 0 ≤ D := by rw [hDdef]; positivity
      simp [this]
    rw [intervalIntegral.integral_congr this]; simp
  have h1 : ∫ x in c..m, debtInv c D x = ∫ x in c..m, (x - c) ^ 2 / 4 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hm1] at hx
    have hxc : 0 ≤ x - c := by linarith [hx.1]
    have hxm : x - c ≤ δ * L := by rw [hmdef] at hx; linarith [hx.2]
    have : (x - c) ^ 2 ≤ (δ * L) ^ 2 := pow_le_pow_left₀ hxc hxm 2
    unfold debtInv pim
    rw [max_eq_left hxc]
    apply min_eq_left
    rw [hDdef]
    nlinarith
  have h2 : ∫ x in m..θ, debtInv c D x = ∫ x in m..θ, D := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hm2] at hx
    have hxc : δ * L ≤ x - c := by rw [hmdef] at hx; linarith [hx.1]
    have hx0 : 0 ≤ x - c := le_trans (by positivity) hxc
    have : (δ * L) ^ 2 ≤ (x - c) ^ 2 := pow_le_pow_left₀ (by positivity) hxc 2
    unfold debtInv pim
    rw [max_eq_left hx0]
    apply min_eq_right
    rw [hDdef]
    nlinarith
  have hsplit : ∫ x in (0:ℝ)..θ, debtInv c D x
      = (∫ x in c..m, (x - c) ^ 2 / 4) + (∫ x in m..θ, D) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := c)
        ((TFDH.cont_debtInv c D).intervalIntegrable _ _) ((TFDH.cont_debtInv c D).intervalIntegrable _ _), hz, zero_add,
      ← intervalIntegral.integral_add_adjacent_intervals (a := c) (b := m) (c := θ)
        ((TFDH.cont_debtInv c D).intervalIntegrable _ _) ((TFDH.cont_debtInv c D).intervalIntegrable _ _), h1, h2]
  have hA : ∫ x in c..m, 1 / θ * ((x - c) ^ 2 / 4) = 1 / θ * ((m - c) ^ 3 / 12) := by
    rw [intervalIntegral.integral_const_mul, TFDH.int_sq]
  have hB : ∫ _x in m..θ, 1 / θ * D = (θ - m) * (1 / θ * D) := by
    simp
    ring
  have hexp : expect θ (debtInv c D) = (∫ x in c..m, 1 / θ * ((x - c) ^ 2 / 4)) + (∫ _x in m..θ, 1 / θ * D) := by
    unfold expect
    rw [hsplit, hA, hB, TFDH.int_sq]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    field_simp
  refine ⟨by rw [hexp], ?_⟩
  rw [hexp, hA, hB, hmdef, hDdef, hLdef]
  field_simp
  ring
