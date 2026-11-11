-- Prove2me | solution 1 for ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_annulusRamp_vanish_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T07:55:41.164194+00:00
-- url     : https://prove2.me/submissions/834f6e50-c5ae-4655-92a7-6833ae4feb4a

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat32_annulusRamp_properties
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (hn : 2 ≤ n) :
    ∃ r > (0 : ℝ), ∀ x, |x| < r → max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|x| - ρ)| - ρ / (n + 1 : ℝ))) = 0 := by
  refine ⟨ρ / (n + 1 : ℝ), by positivity, fun x hx => ?_⟩
  apply (ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_annulusRamp_properties
    ρ hρ n).2.2
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hn_cast : (3 : ℝ) ≤ n + 1 := by
    exact_mod_cast Nat.add_le_add_right hn 1
  have hratio : ρ / (n + 1 : ℝ) ≤ ρ / 3 := by
    rw [div_le_div_iff₀ hn1 (by norm_num : (0 : ℝ) < 3)]
    nlinarith [mul_nonneg hρ.le (sub_nonneg.mpr hn_cast)]
  have hxρ : |x| < ρ := by linarith
  have hneg : |x| - ρ < 0 := by linarith
  rw [abs_of_neg hneg, neg_sub]
  have hbound : 2 * ρ / (n + 1 : ℝ) + ρ / (n + 1 : ℝ) ≤ ρ := by
    rw [← add_div, show (2 : ℝ) * ρ + ρ = 3 * ρ from by ring,
      div_le_iff₀ hn1]
    nlinarith [mul_nonneg hρ.le (sub_nonneg.mpr hn_cast)]
  linarith
