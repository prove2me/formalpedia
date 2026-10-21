-- Prove2me | solution 1 for SkillData.GoldRush.x_limit
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T01:17:28.318561+00:00
-- url     : https://prove2.me/submissions/434ca7f4-1cca-4d27-b92a-817ad455a67b

import Mathlib
import Definitions.Def_SkillData_GoldRush_Model

open SkillData.GoldRush

theorem solution (P : Params) (hP : P.Standing) (lam α : ℝ) (hlam : 0 < lam) (hα : 0 < α) :
    ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ τη : ℝ, T ≤ τη → ∀ x : ℝ, 0 < x → Eq14 P τη x lam α →
      |x - 2 * α * P.γ / (lam * (P.ZH + P.ZL))| < ε := by
  obtain ⟨hθ, hu, hγ, -, -, hZL, hZ⟩ := hP
  intro ε hε
  have hZH : 0 < P.ZH := by linarith
  have hS : 0 < P.ZH + P.ZL := by linarith
  have hΔ : 0 < P.ZH - P.ZL := by linarith
  set S := P.ZH + P.ZL with hSdef
  set Q := P.τu * α ^ 2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set x0 := 2 * α * P.γ / (lam * S) with hx0
  have hx0pos : 0 < x0 := by positivity
  set B := 2 * x0 * (1 + Q) with hB
  have hBpos : 0 < B := by positivity
  set N := B ^ 2 * P.ZL * (P.ZH - P.ZL) / S + x0 * (B * P.ZH + Q) with hN
  have hNpos : 0 < N := by positivity
  clear_value S Q x0 B N
  refine ⟨max (max 1 (2 * x0 * P.ZH)) (N / ε + 1), ?_⟩
  intro τη hT x hx h14
  have hT1 : 1 ≤ τη := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT2 : 2 * x0 * P.ZH ≤ τη := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT3 : N / ε + 1 ≤ τη := le_trans (le_max_right _ _) hT
  have hτ : 0 < τη := by linarith
  have hD : 0 < x * P.ZL + Q + τη := by positivity
  set r := x * P.ZL * (P.ZH - P.ZL) / (x * P.ZL + Q + τη) with hr
  have hr0 : 0 ≤ r := by positivity
  have hrτ : τη * r ≤ x * P.ZL * (P.ZH - P.ZL) := by
    rw [hr, mul_div_assoc']
    rw [div_le_iff₀ hD]
    have : 0 ≤ x * P.ZL * (P.ZH - P.ZL) := by positivity
    have : 0 ≤ x * P.ZL + Q := by positivity
    nlinarith [mul_nonneg ‹0 ≤ x * P.ZL * (P.ZH - P.ZL)› this]
  have h14' : P.γ * α * (x * P.ZH + Q + τη) - 1 / 2 * x * lam * τη * (S + r) = 0 := by
    unfold Eq14 at h14; rw [hr, hSdef, hQ]; exact h14
  have hkey : τη * (x - x0) = x0 * (x * P.ZH + Q) - x * (τη * r) / S := by
    have hx0' : x0 * (lam * S) = 2 * α * P.γ := by
      rw [hx0]; field_simp
    have e : x * (τη * r) / S * S = x * (τη * r) := div_mul_cancel₀ _ hS.ne'
    have hlS : lam * S ≠ 0 := by positivity
    apply mul_left_cancel₀ hlS
    linear_combination (-2) * h14' - (τη + x * P.ZH + Q) * hx0' + lam * e
  have hup : τη * (x - x0) ≤ x0 * (x * P.ZH + Q) := by
    have : 0 ≤ x * (τη * r) / S := by positivity
    linarith
  have hlo : - (x * (x * P.ZL * (P.ZH - P.ZL)) / S) ≤ τη * (x - x0) := by
    have : x * (τη * r) / S ≤ x * (x * P.ZL * (P.ZH - P.ZL)) / S := by
      apply div_le_div_of_nonneg_right _ hS.le
      exact mul_le_mul_of_nonneg_left hrτ hx.le
    have : 0 ≤ x0 * (x * P.ZH + Q) := by positivity
    linarith
  have hxB : x ≤ B := by
    have h1 : x0 * x * P.ZH * 2 ≤ τη * x := by nlinarith
    have h2 : x0 * Q ≤ τη * (x0 * Q) := by
      have : 0 ≤ x0 * Q := by positivity
      nlinarith
    have h3 : τη * (x / 2) ≤ τη * (x0 * (1 + Q)) := by nlinarith
    have h4 := le_of_mul_le_mul_left h3 hτ
    rw [hB]; linarith
  have habs : |τη * (x - x0)| ≤ N := by
    rw [abs_le]; constructor
    · have : x * (x * P.ZL * (P.ZH - P.ZL)) / S ≤ B ^ 2 * P.ZL * (P.ZH - P.ZL) / S := by
        apply div_le_div_of_nonneg_right _ hS.le
        have hxx : x * x ≤ B ^ 2 := by rw [sq]; exact mul_le_mul hxB hxB hx.le hBpos.le
        have hc : 0 ≤ P.ZL * (P.ZH - P.ZL) := by positivity
        have := mul_le_mul_of_nonneg_right hxx hc
        calc x * (x * P.ZL * (P.ZH - P.ZL)) = x * x * (P.ZL * (P.ZH - P.ZL)) := by ring
          _ ≤ B ^ 2 * (P.ZL * (P.ZH - P.ZL)) := this
          _ = B ^ 2 * P.ZL * (P.ZH - P.ZL) := by ring
      have : 0 ≤ x0 * (B * P.ZH + Q) := by positivity
      linarith
    · have : x0 * (x * P.ZH + Q) ≤ x0 * (B * P.ZH + Q) := by
        apply mul_le_mul_of_nonneg_left _ hx0pos.le
        have := mul_le_mul_of_nonneg_right hxB hZH.le
        linarith
      have : 0 ≤ B ^ 2 * P.ZL * (P.ZH - P.ZL) / S := by positivity
      linarith
  rw [abs_mul, abs_of_pos hτ] at habs
  have hNe : N < ε * τη := by
    have : N / ε < τη := by linarith
    rwa [div_lt_iff₀ hε, mul_comm] at this
  by_contra hc
  have hc' : ε ≤ |x - x0| := le_of_not_gt hc
  have := mul_le_mul_of_nonneg_right hc' hτ.le
  linarith
