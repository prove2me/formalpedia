-- Prove2me | solution 1 for SCInfoDesign.Nested.gammaStar_posteriors
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T19:06:33.086454+00:00
-- url     : https://prove2.me/submissions/a8401539-6446-4353-b206-3544357748d7

import Mathlib
import Definitions.Def_SCInfoDesign_Nested_Setting

open SCInfoDesign.Nested

theorem solution (P : Params)
    (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁) (ha₀0 : 0 ≤ P.a₀) (ha₁0 : 0 ≤ P.a₁)
    (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (p₀ : ℝ) (hp₀ : p₀ ∈ Set.Icc (0:ℝ) 1) (hξτ : P.ξ < P.τlow p₀) :
    IsPolicy (P.gammaStar p₀) ∧
    msgProb p₀ (P.gammaStar p₀) 0 = (p₀ - P.pHat) / (1 - P.pHat) ∧
    posterior p₀ (P.gammaStar p₀) 0 = 1 ∧
    (p₀ < 1 → posterior p₀ (P.gammaStar p₀) 1 = P.pHat) := by
  obtain ⟨hp0, hp1⟩ := hp₀
  have hL : 0 < P.b₀ - P.a₀ := by linarith
  have hτ : P.ξ * (P.b₀ - P.a₀) < p₀ * (P.a₁ - P.a₀) := by
    unfold Params.τlow at hξτ; rwa [lt_div_iff₀ hL] at hξτ
  have hα : 0 < P.a₁ - P.a₀ := by
    by_contra h; push_neg at h; nlinarith [mul_pos hξ0 hL]
  have hpp : 0 < p₀ := by
    by_contra h; push_neg at h; nlinarith [mul_pos hξ0 hL]
  set x := P.ξ * (P.b₀ - P.a₀) with hx
  have hx0 : 0 < x := mul_pos hξ0 hL
  set α := P.a₁ - P.a₀ with hαd
  have hd : 0 < α - x := by nlinarith
  set q := (1 - p₀) / p₀ * (x / (α - x)) with hq
  have hgs : P.gammaStar p₀ = ![![1 - q, q], ![0, 1]] := rfl
  have hq0 : 0 ≤ q := by
    rw [hq]; apply mul_nonneg (div_nonneg (by linarith) hpp.le) (div_nonneg hx0.le hd.le)
  have hqp : p₀ * q = (1 - p₀) * x / (α - x) := by
    rw [hq]; field_simp
  have hq1 : p₀ * (1 - q) = (p₀ * α - x) / (α - x) := by
    rw [mul_sub, hqp]; field_simp; ring
  have hq1pos : 0 < p₀ * (1 - q) := by
    rw [hq1]; apply div_pos _ hd; nlinarith
  have hq1' : q < 1 := by
    by_contra h; push_neg at h; nlinarith
  have hpH : P.pHat = x / α := rfl
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro ω m
    rw [hgs]
    fin_cases ω <;> fin_cases m <;> simp <;> linarith
  · intro ω
    rw [hgs]
    fin_cases ω <;> simp [Fin.sum_univ_two]
  · unfold msgProb
    rw [hgs]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero]
    rw [hq1, hpH]
    field_simp
  · unfold posterior msgProb
    rw [hgs]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero]
    exact div_self hq1pos.ne'
  · intro hp1'
    unfold posterior msgProb
    rw [hgs]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one]
    rw [hqp, hpH]
    have : 0 < 1 - p₀ := by linarith
    field_simp
    ring
