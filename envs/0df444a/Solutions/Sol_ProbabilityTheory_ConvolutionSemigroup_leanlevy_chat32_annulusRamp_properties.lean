-- Prove2me | solution 1 for ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_annulusRamp_properties
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T00:30:14.857209+00:00
-- url     : https://prove2.me/submissions/854da2d0-9538-4054-977d-c8be872e2d03

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) :
    (∀ x : ℝ, 0 ≤ max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|x| - ρ)| - ρ / (n + 1 : ℝ))) ∧ max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|x| - ρ)| - ρ / (n + 1 : ℝ))) ≤ 1) ∧
    (∀ x : ℝ, |(|x| - ρ)| ≤ ρ / (n + 1 : ℝ) → max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|x| - ρ)| - ρ / (n + 1 : ℝ))) = 1) ∧
    (∀ x : ℝ, 2 * ρ / (n + 1 : ℝ) ≤ |(|x| - ρ)| → max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|x| - ρ)| - ρ / (n + 1 : ℝ))) = 0) := by
  constructor
  · intro x
    constructor
    · exact le_max_left _ _
    · refine max_le zero_le_one ?_
      have h1 : 0 ≤ ((n + 1 : ℝ) / ρ) * max 0 (|(|x| - ρ)| - ρ / (n + 1 : ℝ)) := by positivity
      linarith
  constructor
  · intro x hx
    have hsub : |(|x| - ρ)| - ρ / (n + 1 : ℝ) ≤ 0 := by linarith
    rw [show max 0 (|(|x| - ρ)| - ρ / (n + 1 : ℝ)) = 0 from max_eq_left hsub,
        mul_zero, sub_zero, max_eq_right zero_le_one]
  · intro x hx
    have hn1 : (0 : ℝ) < n + 1 := by positivity
    have h_diff : ρ / (n + 1 : ℝ) ≤ |(|x| - ρ)| - ρ / (n + 1 : ℝ) := by
      have h : 2 * ρ / (n + 1 : ℝ) =
          ρ / (n + 1 : ℝ) + ρ / (n + 1 : ℝ) := by ring
      linarith [h ▸ hx]
    have h_nn : 0 ≤ |(|x| - ρ)| - ρ / (n + 1 : ℝ) :=
      le_trans (by positivity) h_diff
    rw [max_eq_right h_nn]
    have h_prod : 1 ≤ ((n + 1 : ℝ) / ρ) *
        (|(|x| - ρ)| - ρ / (n + 1 : ℝ)) := by
      have h := mul_le_mul_of_nonneg_left h_diff
        (by positivity : (0 : ℝ) ≤ (n + 1 : ℝ) / ρ)
      rw [show ((n + 1 : ℝ) / ρ) * (ρ / (n + 1 : ℝ)) = 1 from by field_simp] at h
      exact h
    have hneg : 1 - ((n + 1 : ℝ) / ρ) *
        (|(|x| - ρ)| - ρ / (n + 1 : ℝ)) ≤ 0 := by linarith
    exact max_eq_left hneg
