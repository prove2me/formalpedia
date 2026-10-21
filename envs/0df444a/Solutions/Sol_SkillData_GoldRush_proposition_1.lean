-- Prove2me | solution 1 for SkillData.GoldRush.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T01:11:38.923038+00:00
-- url     : https://prove2.me/submissions/a63a7a3e-510f-4919-91ca-5b5b671fc88c

import Mathlib
import Definitions.Def_SkillData_GoldRush_Model

open SkillData.GoldRush

theorem solution (P : Params) (hP : P.Standing) (τη x lam : ℝ) (hτη : 0 < τη)
    (hx : 0 < x) (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    ∃! α : ℝ, 0 < α ∧ Eq14 P τη x lam α := by
  obtain ⟨hθ, hu, hγ, -, -, hZL, hZ⟩ := hP
  set f : ℝ → ℝ := fun α => P.γ * α * (x * P.ZH + P.τu * α ^ 2 + τη)
    - 1 / 2 * x * lam * τη *
      (P.ZH + P.ZL + x * P.ZL * (P.ZH - P.ZL) / (x * P.ZL + P.τu * α ^ 2 + τη)) with hf
  have hK : 0 < x * P.ZL * (P.ZH - P.ZL) := by
    have := sub_pos.mpr hZ; positivity
  have hmono : ∀ a b : ℝ, 0 ≤ a → a < b → f a < f b := by
    intro a b ha hab
    have hb : 0 < b := lt_of_le_of_lt ha hab
    have h1 : P.γ * a * (x * P.ZH + P.τu * a ^ 2 + τη) < P.γ * b * (x * P.ZH + P.τu * b ^ 2 + τη) := by
      have hab2 : a ^ 2 ≤ b ^ 2 := by nlinarith
      have hpos : 0 < x * P.ZH + P.τu * a ^ 2 + τη := by
        have : 0 < x * P.ZH := by nlinarith
        positivity
      have : P.τu * a ^ 2 ≤ P.τu * b ^ 2 := mul_le_mul_of_nonneg_left hab2 hu.le
      have e1 : P.γ * a * (x * P.ZH + P.τu * a ^ 2 + τη) < P.γ * b * (x * P.ZH + P.τu * a ^ 2 + τη) := by
        apply mul_lt_mul_of_pos_right _ hpos; exact mul_lt_mul_of_pos_left hab hγ
      have e2 : P.γ * b * (x * P.ZH + P.τu * a ^ 2 + τη) ≤ P.γ * b * (x * P.ZH + P.τu * b ^ 2 + τη) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      linarith
    have h2 : x * P.ZL * (P.ZH - P.ZL) / (x * P.ZL + P.τu * b ^ 2 + τη)
        ≤ x * P.ZL * (P.ZH - P.ZL) / (x * P.ZL + P.τu * a ^ 2 + τη) := by
      apply div_le_div_of_nonneg_left hK.le (by positivity)
      have : a ^ 2 ≤ b ^ 2 := by nlinarith
      nlinarith
    have hc : 0 < 1 / 2 * x * lam * τη := by positivity
    simp only [hf]
    nlinarith [mul_le_mul_of_nonneg_left h2 hc.le]
  have hcont : Continuous f := by
    simp only [hf]
    apply Continuous.sub (by fun_prop)
    apply Continuous.mul (by fun_prop)
    apply Continuous.add (by fun_prop)
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro α; have : 0 < x * P.ZL := by positivity
    positivity
  -- existence via IVT
  have hf0 : f 0 < 0 := by
    simp only [hf]
    have : 0 < 1 / 2 * x * lam * τη * (P.ZH + P.ZL + x * P.ZL * (P.ZH - P.ZL) /
        (x * P.ZL + P.τu * 0 ^ 2 + τη)) := by
      have : 0 < x * P.ZL + P.τu * 0 ^ 2 + τη := by positivity
      have : 0 < P.ZH := by linarith
      positivity
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_neg] at this ⊢
    simpa using this
  set M : ℝ := 1 / 2 * x * lam * τη * (P.ZH + P.ZL + x * P.ZL * (P.ZH - P.ZL) / (x * P.ZL + τη)) with hM
  set A : ℝ := M / (P.γ * τη) + 1 with hA
  have hMpos : 0 < M := by
    have : 0 < P.ZH := by linarith
    have : 0 < x * P.ZL + τη := by positivity
    positivity
  have hApos : 0 < A := by positivity
  have hfA : 0 < f A := by
    simp only [hf]
    have h2 : x * P.ZL * (P.ZH - P.ZL) / (x * P.ZL + P.τu * A ^ 2 + τη)
        ≤ x * P.ZL * (P.ZH - P.ZL) / (x * P.ZL + τη) := by
      apply div_le_div_of_nonneg_left hK.le (by positivity)
      have : 0 ≤ P.τu * A ^ 2 := by positivity
      linarith
    have hc : 0 < 1 / 2 * x * lam * τη := by positivity
    have h3 : 1 / 2 * x * lam * τη * (P.ZH + P.ZL + x * P.ZL * (P.ZH - P.ZL) / (x * P.ZL + P.τu * A ^ 2 + τη)) ≤ M := by
      rw [hM]; nlinarith [mul_le_mul_of_nonneg_left h2 hc.le]
    have h4 : P.γ * A * τη > M := by
      rw [hA]; field_simp; nlinarith [mul_pos hγ hτη]
    have h5 : P.γ * A * τη ≤ P.γ * A * (x * P.ZH + P.τu * A ^ 2 + τη) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : 0 < x * P.ZH := by nlinarith
      nlinarith [sq_nonneg A, mul_nonneg hu.le (sq_nonneg A)]
    linarith
  obtain ⟨α, hαI, hα⟩ : ∃ α ∈ Set.Icc (0:ℝ) A, f α = 0 :=
    intermediate_value_Icc hApos.le hcont.continuousOn ⟨hf0.le, hfA.le⟩
  have hαpos : 0 < α := by
    rcases eq_or_lt_of_le hαI.1 with h | h
    · rw [← h] at hα; linarith
    · exact h
  refine ⟨α, ⟨hαpos, hα⟩, ?_⟩
  rintro β ⟨hβ, hβe⟩
  have hβe' : f β = 0 := hβe
  rcases lt_trichotomy β α with h | h | h
  · have := hmono β α hβ.le h; linarith
  · exact h
  · have := hmono α β hαpos.le h; linarith
