-- Prove2me | solution 1 for ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_upperRamp_vanish_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T08:11:37.994191+00:00
-- url     : https://prove2.me/submissions/939df1b7-3a25-4511-8151-7880e843b881

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A uniformly positive neighbourhood of zero is annihilated by every
upper ramp with index at least one. -/
theorem solution (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (hn : 1 ≤ n) :
    ∃ r > (0 : ℝ), ∀ x, |x| < r →
      min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) = 0 := by
  refine ⟨ρ / 2, by positivity, ?_⟩
  intro x hx
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdiff : 0 ≤ ρ - |x| := by linarith
  have hn2 : (2 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hmul : (ρ - |x|) * 2 ≤ (ρ - |x|) * ((n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hn2 hdiff
  have hδ : ρ ≤ (ρ - |x|) * 2 := by linarith
  have hnum : (|x| - ρ) * ((n : ℝ) + 1) ≤ -ρ := by
    nlinarith [hmul, hδ]
  have hdiv : (|x| - ρ) * (((n : ℝ) + 1) / ρ) ≤ -1 := by
    calc
      (|x| - ρ) * (((n : ℝ) + 1) / ρ) =
          ((|x| - ρ) * ((n : ℝ) + 1)) / ρ := by ring
      _ ≤ -1 := (div_le_iff₀ hρ).2 (by nlinarith [hnum])
  have hnonpos : (|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1 ≤ 0 := by
    convert add_le_add_right hdiv 1 using 1 <;> push_cast <;> ring
  have hz : max (0 : ℝ) ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1) = 0 :=
    max_eq_left hnonpos
  simp [hz]
