-- Prove2me | solution 1 for QuantumEcon.Duopoly.eq11_12_intercept_effect
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:26:59.568995+00:00
-- url     : https://prove2.me/submissions/2cef4507-d205-434c-88fa-99b06124ca67

import Mathlib
import Definitions.Def_QuantumEcon_Duopoly_Setting
set_option autoImplicit false
open QuantumEcon.Duopoly

theorem solution (a c γ : ℝ)
    (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ 1) (hc₁ : 1 < c) (hcc : c < c ^ 2)
    (hca : c ^ 2 < a)
    (hq₁ : 0 < (a * (-2 + γ) + c * (2 - c * γ)) / (-4 + γ ^ 2))
    (hq₂ : 0 < (c * (2 * c - γ) + a * (-2 + γ)) / (-4 + γ ^ 2)) :
    let π₁ : ℝ → ℝ := fun z =>
      (z * (-2 + γ) + c * (2 - c * γ)) ^ 2 / (-4 + γ ^ 2) ^ 2
    let π₂ : ℝ → ℝ := fun z =>
      (c * (2 * c - γ) + z * (-2 + γ)) ^ 2 / (-4 + γ ^ 2) ^ 2
    HasDerivAt π₁
      (2 * (-2 + γ) * (a * (-2 + γ) + c * (2 - c * γ)) /
        (-4 + γ ^ 2) ^ 2) a ∧
    HasDerivAt π₂
      (2 * (c * (2 * c - γ) + a * (-2 + γ)) * (-2 + γ) /
        (-4 + γ ^ 2) ^ 2) a ∧
    0 < deriv π₂ a ∧ deriv π₂ a < deriv π₁ a := by
  intro π₁ π₂
  have hD : -4 + γ ^ 2 < 0 := by nlinarith
  have hD2 : 0 < (-4 + γ ^ 2) ^ 2 := by rw [sq]; exact mul_pos_of_neg_of_neg hD hD
  have hg : -2 + γ < 0 := by linarith
  have h1 : HasDerivAt π₁
      (2 * (-2 + γ) * (a * (-2 + γ) + c * (2 - c * γ)) / (-4 + γ ^ 2) ^ 2) a := by
    have h := ((((hasDerivAt_id a).mul_const (-2 + γ)).add_const (c * (2 - c * γ))).pow 2).div_const
      ((-4 + γ ^ 2) ^ 2)
    refine h.congr_deriv ?_
    simp only [id]
    norm_num
    try ring
  have h2 : HasDerivAt π₂
      (2 * (c * (2 * c - γ) + a * (-2 + γ)) * (-2 + γ) / (-4 + γ ^ 2) ^ 2) a := by
    have h := ((((hasDerivAt_id a).mul_const (-2 + γ)).const_add (c * (2 * c - γ))).pow 2).div_const
      ((-4 + γ ^ 2) ^ 2)
    refine h.congr_deriv ?_
    simp only [id]
    norm_num
    try ring
  refine ⟨h1, h2, ?_⟩
  rw [h1.deriv, h2.deriv]
  have e1 : a * (-2 + γ) + c * (2 - c * γ) < 0 := by
    have := (div_pos_iff.mp hq₁)
    rcases this with ⟨_, h⟩ | ⟨h, _⟩
    · linarith
    · exact h
  have e2 : c * (2 * c - γ) + a * (-2 + γ) < 0 := by
    have := (div_pos_iff.mp hq₂)
    rcases this with ⟨_, h⟩ | ⟨h, _⟩
    · linarith
    · exact h
  have e3 : a * (-2 + γ) + c * (2 - c * γ) < c * (2 * c - γ) + a * (-2 + γ) := by
    nlinarith [mul_pos (by linarith : 0 < c) (by linarith : 0 < c - 1), mul_nonneg hγ₀ (mul_pos (by linarith : 0 < c) (by linarith : 0 < c - 1)).le]
  constructor
  · apply div_pos _ hD2
    nlinarith
  · apply div_lt_div_of_pos_right _ hD2
    nlinarith
