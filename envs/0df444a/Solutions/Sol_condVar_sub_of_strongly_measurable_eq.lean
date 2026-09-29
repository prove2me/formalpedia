-- Prove2me | solution 1 for condVar_sub_of_strongly_measurable_eq
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-06-24T01:48:07.443985+00:00
-- url     : https://prove2.me/submissions/d6d7c863-402b-4a25-81e0-b5dff3896530

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

theorem solution
    {Ω : Type*} {m₀ m : MeasurableSpace Ω} {μ : Measure[m₀] Ω}
    (hm : m ≤ m₀) [IsFiniteMeasure μ]
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hYm : StronglyMeasurable[m] Y) :
    Var[fun ω => X ω - Y ω; μ | m] =ᵐ[μ] Var[X; μ | m] := by
  have hXint : Integrable X μ := hX.integrable one_le_two
  have hYint : Integrable Y μ := hY.integrable one_le_two
  have hcondsub : μ[(fun ω => X ω - Y ω) | m] =ᵐ[μ] fun ω => (μ[X | m]) ω - Y ω := by
    have hXYfun : (fun ω => X ω - Y ω) = X - Y := by funext ω; simp [Pi.sub_apply]
    have h1 : μ[(X - Y) | m] =ᵐ[μ] μ[X | m] - μ[Y | m] := condExp_sub hXint hYint _
    have h2 : μ[Y | m] = Y := condExp_of_stronglyMeasurable hm hYm hYint
    rw [hXYfun]
    filter_upwards [h1] with ω hω1
    simp only [Pi.sub_apply] at hω1 ⊢
    rw [hω1, h2]
  rw [condVar, condVar]
  refine condExp_congr_ae ?_
  filter_upwards [hcondsub] with ω hω
  simp only [Pi.pow_apply, Pi.sub_apply] at hω ⊢
  rw [hω]
  ring
