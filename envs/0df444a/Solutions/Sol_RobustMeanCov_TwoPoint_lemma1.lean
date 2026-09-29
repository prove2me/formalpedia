-- Prove2me | solution 1 for RobustMeanCov.TwoPoint.lemma1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:49:49.843186+00:00
-- url     : https://prove2.me/submissions/6f6326fd-d306-4e3c-bbf1-82a4a53ea8e9

import Mathlib
import Definitions.Def_RobustMeanCov_TwoPoint_TwoPointSupport
import Definitions.Def_RobustMeanCov_TwoPoint_Lemma1Quadratic

namespace RobustMeanCov.TwoPoint

/-- The Lemma 1 quadratic built from the endpoint slopes of `A y² + B y + C` is that quadratic,
provided it interpolates `u` at `a` and `b`. -/
theorem aux_tpl1_quad_eq (u : ℝ → ℝ) (a b A B C : ℝ) (hab : a < b)
    (ha : A * a ^ 2 + B * a + C = u a) (hb : A * b ^ 2 + B * b + C = u b) (y : ℝ) :
    lemma1Quad u a b (2 * A * a + B) (2 * A * b + B) y = A * y ^ 2 + B * y + C := by
  have hne : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
  unfold lemma1Quad lemma1A lemma1B lemma1C
  rw [← ha, ← hb]
  field_simp
  ring

/-- Values of the Lemma 1 quadratic at the endpoints. -/
theorem aux_tpl1_quad_a (u : ℝ → ℝ) (a b qa qb : ℝ) (hab : a < b)
    (hs : (u b - u a) / (b - a) = (qa + qb) / 2) :
    lemma1Quad u a b qa qb a = u a := by
  have hne : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
  unfold lemma1Quad lemma1A lemma1B lemma1C
  rw [div_eq_iff hne] at hs
  field_simp
  linear_combination (-(2:ℝ) * a) * hs

theorem aux_tpl1_quad_b (u : ℝ → ℝ) (a b qa qb : ℝ) (hab : a < b)
    (hs : (u b - u a) / (b - a) = (qa + qb) / 2) :
    lemma1Quad u a b qa qb b = u b := by
  have hne : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
  unfold lemma1Quad lemma1A lemma1B lemma1C
  rw [div_eq_iff hne] at hs
  field_simp
  linear_combination (-(2:ℝ) * b) * hs

end RobustMeanCov.TwoPoint

open RobustMeanCov.TwoPoint

theorem solution (u : ℝ → ℝ) :
    TwoPointSupport u ↔
      ∀ μ σ : ℝ, 0 < σ →
        ∃ a b qa qb : ℝ, a < b ∧
          (b - μ) * (μ - a) = σ ^ 2 ∧
          (u b - u a) / (b - a) = (qa + qb) / 2 ∧
          ∀ y : ℝ, lemma1Quad u a b qa qb y ≤ u y := by
  constructor
  · intro h μ σ hσ
    obtain ⟨a, b, A, B, C, hab, hS, ha, hb, p, hp, hμ, hv⟩ := h μ σ hσ
    have hne : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
    refine ⟨a, b, 2 * A * a + B, 2 * A * b + B, hab, ?_, ?_, ?_⟩
    · subst hμ
      linear_combination hv
    · rw [div_eq_iff hne, ← ha, ← hb]
      ring
    · intro y
      rw [aux_tpl1_quad_eq u a b A B C hab ha hb y]
      exact hS y
  · intro h μ σ hσ
    obtain ⟨a, b, qa, qb, hab, hvar, hs, hq⟩ := h μ σ hσ
    have hba : 0 < b - a := sub_pos.mpr hab
    have hne : b - a ≠ 0 := ne_of_gt hba
    have hσ2 : 0 < σ ^ 2 := by positivity
    have hμa : a < μ := by
      by_contra hc'
      have hc : μ ≤ a := not_lt.mp hc'
      have h1 : 0 ≤ a - μ := by linarith
      have h2 : 0 ≤ b - μ := by linarith
      nlinarith [mul_nonneg h1 h2]
    have hμb : μ < b := by
      by_contra hc'
      have hc : b ≤ μ := not_lt.mp hc'
      have h1 : 0 ≤ μ - b := by linarith
      have h2 : 0 ≤ μ - a := by linarith
      nlinarith [mul_nonneg h1 h2]
    refine ⟨a, b, lemma1A a b qa qb, lemma1B a b qa qb, lemma1C u a b qa qb, hab, ?_, ?_, ?_, ?_⟩
    · intro y
      exact hq y
    · exact aux_tpl1_quad_a u a b qa qb hab hs
    · exact aux_tpl1_quad_b u a b qa qb hab hs
    · refine ⟨(b - μ) / (b - a), ⟨?_, ?_⟩, ?_, ?_⟩
      · apply div_pos <;> linarith
      · rw [div_lt_one hba]; linarith
      · field_simp
        ring
      · rw [← hvar]
        field_simp
        ring
