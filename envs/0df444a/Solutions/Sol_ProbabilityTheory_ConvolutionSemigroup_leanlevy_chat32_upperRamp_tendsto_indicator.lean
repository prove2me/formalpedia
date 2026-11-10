-- Prove2me | solution 1 for ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_upperRamp_tendsto_indicator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T00:25:01.690263+00:00
-- url     : https://prove2.me/submissions/1cb4c8c8-3a36-4683-8952-8423eb3833ba

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat32_upperRamp_eq_one
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat32_upperRamp_eq_zero
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution (ρ : ℝ) (hρ : 0 < ρ) (x : ℝ) :
    Tendsto (fun n : ℕ => min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1))) atTop
      (𝓝 (Set.indicator {y : ℝ | ρ ≤ |y|} (fun _ => (1 : ℝ)) x)) := by
  by_cases hx : ρ ≤ |x|
  · rw [Set.indicator_of_mem (show x ∈ {y | ρ ≤ |y|} from hx)]
    refine tendsto_atTop_of_eventually_const (i₀ := 0) (fun n _ => ?_)
    exact ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_upperRamp_eq_one ρ hρ n x hx
  · push Not at hx
    rw [Set.indicator_of_notMem (show x ∉ {y | ρ ≤ |y|} from not_le.mpr hx)]
    have h_pos : 0 < ρ - |x| := by linarith
    obtain ⟨N, hN⟩ := exists_nat_gt (ρ / (ρ - |x|))
    rw [div_lt_iff₀ h_pos] at hN
    refine tendsto_atTop_of_eventually_const (i₀ := N) (fun n hn => ?_)
    apply ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_upperRamp_eq_zero ρ hρ n x
    have hn1_pos : (0 : ℝ) < n + 1 := by positivity
    have hN_le : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h1 : ρ ≤ (ρ - |x|) * (n + 1 : ℝ) := by
      calc ρ ≤ (N : ℝ) * (ρ - |x|) := le_of_lt hN
        _ ≤ (n : ℝ) * (ρ - |x|) := mul_le_mul_of_nonneg_right hN_le h_pos.le
        _ ≤ (n + 1 : ℝ) * (ρ - |x|) :=
            mul_le_mul_of_nonneg_right (by linarith) h_pos.le
        _ = (ρ - |x|) * (n + 1 : ℝ) := by ring
    rw [← div_le_iff₀ hn1_pos] at h1
    linarith
