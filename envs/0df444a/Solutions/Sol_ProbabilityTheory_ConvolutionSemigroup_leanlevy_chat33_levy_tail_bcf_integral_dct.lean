-- Prove2me | solution 1 for ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_levy_tail_bcf_integral_dct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T07:38:58.983514+00:00
-- url     : https://prove2.me/submissions/c458d51b-5051-4883-8e4f-b1ec9e041eee

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_LeanLevy_Levy_LevyMeasure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution {ν : Measure ℝ} (hν : IsLevyMeasure ν)
    {ρ : ℝ} (hρ : 0 < ρ)
    (f : ℕ → BoundedContinuousFunction ℝ ℝ) (M : ℝ)
    (hf_bound : ∀ n x, |f (n + 1) x| ≤ M)
    (hf_support : ∀ n x, |x| < ρ → f (n + 1) x = 0)
    (g : ℝ → ℝ)
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop
      (𝓝 (Set.indicator (largeSet ρ) g x))) :
    Tendsto (fun n => ∫ x, f n x ∂ν) atTop
      (𝓝 (∫ x in largeSet ρ, g x ∂ν)) := by
  have hmeas : MeasurableSet (largeSet ρ) :=
    (isClosed_le continuous_const continuous_abs).measurableSet
  haveI : IsFiniteMeasure (ν.restrict (largeSet ρ)) :=
    isFiniteMeasure_restrict.mpr (hν.measure_setOf_abs_ge_lt_top hρ).ne
  have hbound : Integrable (Set.indicator (largeSet ρ) (fun _ => M)) ν :=
    (integrable_indicator_iff hmeas).mpr (integrable_const M)
  have hshift : Tendsto (fun n => ∫ x, f (n + 1) x ∂ν) atTop
      (𝓝 (∫ x, Set.indicator (largeSet ρ) g x ∂ν)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (bound := Set.indicator (largeSet ρ) (fun _ => M))
      (fun n => (f (n + 1)).continuous.aestronglyMeasurable)
      hbound
      (fun n => Filter.Eventually.of_forall (fun x => ?_))
      (Filter.Eventually.of_forall (fun x =>
        (tendsto_add_atTop_iff_nat 1).mpr (hlim x)))
    rw [Real.norm_eq_abs]
    by_cases hx : x ∈ largeSet ρ
    · rw [Set.indicator_of_mem hx]
      exact hf_bound n x
    · rw [Set.indicator_of_notMem hx]
      have hxsmall : |x| < ρ := by
        change ¬ ρ ≤ |x| at hx
        exact lt_of_not_ge hx
      rw [hf_support n x hxsmall, abs_zero]
  rw [integral_indicator hmeas] at hshift
  exact (tendsto_add_atTop_iff_nat
    (f := fun n => ∫ x, f n x ∂ν) 1).mp hshift
