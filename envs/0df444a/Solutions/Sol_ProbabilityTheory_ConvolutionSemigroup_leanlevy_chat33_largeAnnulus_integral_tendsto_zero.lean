-- Prove2me | solution 1 for ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_largeAnnulus_integral_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T07:59:10.088196+00:00
-- url     : https://prove2.me/submissions/9bec2972-26e0-43ec-98fe-8f52bd509f52

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat32_exists_annulusBCF
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat32_annulusRamp_properties
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat32_annulusRamp_tendsto_indicator
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat33_levy_tail_bcf_dct_general
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution (ρ : ℝ) (hρ : 0 < ρ)
    {ν : Measure ℝ} (hν : IsLevyMeasure ν)
    (hν_atom : ν {x | |x| = ρ} = 0) :
    ∃ f : ℕ → BoundedContinuousFunction ℝ ℝ,
      (∀ n x, f n x = max 0 (1 - ((n + 2 : ℝ) / ρ) *
        max 0 (|(|x| - ρ)| - ρ / (n + 2 : ℝ)))) ∧
      Tendsto (fun n => ∫ x, f n x ∂ν) atTop (𝓝 0) := by
  classical
  let φ : ℕ → BoundedContinuousFunction ℝ ℝ := fun n =>
    Classical.choose (ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_exists_annulusBCF
      ρ hρ (n + 1))
  have hφ : ∀ n x, φ n x = max 0 (1 - ((n + 2 : ℝ) / ρ) *
      max 0 (|(|x| - ρ)| - ρ / (n + 2 : ℝ))) := by
    intro n x
    have h := (Classical.choose_spec
      (ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_exists_annulusBCF
        ρ hρ (n + 1))) x
    convert h using 1 <;> push_cast <;> ring
  have hφ_bound : ∀ n x, |φ (n + 1) x| ≤ 1 := by
    intro n x
    have hchoice := (Classical.choose_spec
      (ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_exists_annulusBCF
        ρ hρ ((n + 1) + 1))) x
    rw [hchoice,
      abs_of_nonneg ((ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_annulusRamp_properties
        ρ hρ ((n + 1) + 1)).1 x).1]
    exact ((ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_annulusRamp_properties
      ρ hρ ((n + 1) + 1)).1 x).2
  have hφ_support : ∀ n x, |x| < ρ / 3 → φ (n + 1) x = 0 := by
    intro n x hx
    have hden : 0 < (n : ℝ) + 3 := by positivity
    have hratio : 2 * ρ / ((n : ℝ) + 3) ≤ 2 * ρ / 3 :=
      (div_le_div_iff_of_pos_left (by positivity) hden (by norm_num)).mpr
        (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    have hxρ : |x| < ρ := by linarith
    have habs : |(|x| - ρ)| = ρ - |x| := by
      rw [abs_of_nonpos (by linarith : |x| - ρ ≤ 0)]
      ring
    have hbound : 2 * ρ / ((((n + 1 : ℕ) + 1 : ℕ) : ℝ) + 1) ≤ |(|x| - ρ)| := by
      have hcast : ((((n + 1 : ℕ) + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 3 := by
        push_cast
        ring
      rw [hcast, habs]
      linarith
    have hzero := (ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_annulusRamp_properties
      ρ hρ ((n + 1) + 1)).2.2 x hbound
    have hchoice := (Classical.choose_spec
      (ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_exists_annulusBCF
        ρ hρ ((n + 1) + 1))) x
    rw [hchoice, hzero]
  have hφ_limit : ∀ x, Tendsto (fun n => φ n x) atTop
      (𝓝 (Set.indicator {y : ℝ | |y| = ρ} (fun _ => (1 : ℝ)) x)) := by
    intro x
    have h := (tendsto_add_atTop_iff_nat 1).mpr
      (ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_annulusRamp_tendsto_indicator ρ hρ x)
    exact h.congr (fun n => by
      rw [hφ n x]
      push_cast
      ring)
  have hρ3 : 0 < ρ / 3 := by positivity
  have h_dct :=
    ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_levy_tail_bcf_dct_general
      hν hρ3 φ 1 hφ_bound hφ_support
      (Set.indicator {y : ℝ | |y| = ρ} (fun _ => (1 : ℝ))) hφ_limit
  have hmeas : MeasurableSet {y : ℝ | |y| = ρ} :=
    (isClosed_singleton.preimage continuous_abs).measurableSet
  rw [integral_indicator hmeas] at h_dct
  have hzero : ∫ _ in {y : ℝ | |y| = ρ}, (1 : ℝ) ∂ν = 0 := by
    have hrestr : ν.restrict {y : ℝ | |y| = ρ} = 0 := by
      rw [Measure.restrict_eq_zero]
      exact hν_atom
    rw [show (∫ _ in {y : ℝ | |y| = ρ}, (1 : ℝ) ∂ν) =
      ∫ _, (1 : ℝ) ∂(ν.restrict {y : ℝ | |y| = ρ}) from rfl, hrestr,
      integral_zero_measure]
  rw [hzero] at h_dct
  exact ⟨φ, hφ, h_dct⟩