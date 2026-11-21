-- Prove2me | solution 1 for StochMatchPoly.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T02:50:44.274521+00:00
-- url     : https://prove2.me/submissions/de379126-4510-40a5-86f7-b00337d5d316

import Mathlib

open MeasureTheory ProbabilityTheory

universe u

theorem solution :
    (∀ b r : ℝ, 0 < b → max (r - b) 0 ≤ r ^ 2 / (4 * b)) ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ)
      (c : ℝ), MemLp W 2 P → ∫ ω, W ω ∂P < c →
      ∫ ω, max (W ω - c) 0 ∂P ≤ variance W P / (4 * (c - ∫ ω, W ω ∂P)) := by
  have hpart1 : ∀ b r : ℝ, 0 < b → max (r - b) 0 ≤ r ^ 2 / (4 * b) := by
    intro b r hb
    have hb4 : (0 : ℝ) < 4 * b := by linarith
    by_cases h : r ≤ b
    · rw [max_eq_right (by linarith : r - b ≤ 0)]
      positivity
    · have hbr : b < r := not_le.mp h
      rw [max_eq_left (by linarith : (0 : ℝ) ≤ r - b)]
      rw [le_div_iff₀ hb4]
      nlinarith [sq_nonneg (r - 2 * b)]
  refine ⟨hpart1, ?_⟩
  intro Ω _ P _ W c hW hc
  have hb : 0 < c - ∫ ω, W ω ∂P := by linarith
  have hWint : Integrable W P := hW.integrable (q := 2) (by norm_num)
  have hWsub : MemLp (fun ω => W ω - ∫ ω, W ω ∂P) 2 P :=
    hW.sub (memLp_const _)
  have hsq : Integrable (fun ω => (W ω - ∫ ω, W ω ∂P) ^ 2) P := by
    simpa using MemLp.integrable_sq hWsub
  have hgint : Integrable (fun ω => (W ω - ∫ ω, W ω ∂P) ^ 2 / (4 * (c - ∫ ω, W ω ∂P))) P :=
    hsq.div_const _
  have hpt : ∀ x, max (W x - c) 0 ≤ (W x - ∫ ω, W ω ∂P) ^ 2 / (4 * (c - ∫ ω, W ω ∂P)) := by
    intro x
    have h := hpart1 (c - ∫ ω, W ω ∂P) (W x - ∫ ω, W ω ∂P) hb
    simpa [sub_sub_sub_cancel_right] using h
  calc ∫ ω, max (W ω - c) 0 ∂P
      ≤ ∫ ω, (W ω - ∫ ω, W ω ∂P) ^ 2 / (4 * (c - ∫ ω, W ω ∂P)) ∂P :=
        integral_mono_of_nonneg (ae_of_all _ fun ω => le_max_right _ _) hgint (ae_of_all _ hpt)
    _ = (∫ ω, (W ω - ∫ ω, W ω ∂P) ^ 2 ∂P) / (4 * (c - ∫ ω, W ω ∂P)) := by
        rw [integral_div]
    _ = variance W P / (4 * (c - ∫ ω, W ω ∂P)) := by
        rw [← variance_eq_integral hW.aemeasurable]
