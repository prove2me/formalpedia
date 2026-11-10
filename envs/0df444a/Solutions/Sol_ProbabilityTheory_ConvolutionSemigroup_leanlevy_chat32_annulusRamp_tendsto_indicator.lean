-- Prove2me | solution 1 for ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_annulusRamp_tendsto_indicator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T00:36:20.229477+00:00
-- url     : https://prove2.me/submissions/5988f166-cdc1-4b81-82af-afa8770db1f8

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat32_annulusRamp_properties
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution (ρ : ℝ) (hρ : 0 < ρ) (x : ℝ) :
    Tendsto (fun n : ℕ => max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|x| - ρ)| - ρ / (n + 1 : ℝ)))) atTop
      (𝓝 (Set.indicator {y : ℝ | |y| = ρ} (fun _ => (1 : ℝ)) x)) := by
  by_cases hx : |x| = ρ
  · rw [Set.indicator_of_mem (show x ∈ {y | |y| = ρ} from hx)]
    refine tendsto_atTop_of_eventually_const (i₀ := 0) (fun n _ => ?_)
    have hbound : |(|x| - ρ)| ≤ ρ / (n + 1 : ℝ) := by
      rw [hx, sub_self, abs_zero]
      positivity
    exact (ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_annulusRamp_properties
      ρ hρ n).2.1 x hbound
  · rw [Set.indicator_of_notMem (show x ∉ {y | |y| = ρ} from hx)]
    have h_pos : 0 < |(|x| - ρ)| := abs_pos.mpr (sub_ne_zero.mpr hx)
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * ρ / |(|x| - ρ)|)
    rw [div_lt_iff₀ h_pos] at hN
    refine tendsto_atTop_of_eventually_const (i₀ := N) (fun n hn => ?_)
    have hn1_pos : (0 : ℝ) < n + 1 := by positivity
    have hN_le : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 : 2 * ρ ≤ (n + 1 : ℝ) * |(|x| - ρ)| := by
      calc (2 : ℝ) * ρ ≤ (N : ℝ) * |(|x| - ρ)| := le_of_lt hN
        _ ≤ (n : ℝ) * |(|x| - ρ)| := mul_le_mul_of_nonneg_right hN_le h_pos.le
        _ ≤ (n + 1 : ℝ) * |(|x| - ρ)| :=
            mul_le_mul_of_nonneg_right (by linarith) h_pos.le
    have hsmall : 2 * ρ / (n + 1 : ℝ) ≤ |(|x| - ρ)| := by
      rw [div_le_iff₀ hn1_pos]
      linarith
    exact (ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_annulusRamp_properties
      ρ hρ n).2.2 x hsmall
