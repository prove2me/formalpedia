-- Prove2me | solution 1 for TeschlQM.Herglotz.ae_hasMeasureDeriv_rnDeriv
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T22:32:44.469472+00:00
-- url     : https://prove2.me/submissions/f9d07d9f-0431-4f26-b256-306e7d6a0110

import Definitions.Def_TeschlQM_Herglotz_HasMeasureDeriv
import Definitions.Def_TeschlQM_Herglotz_acPart
import Theorems.Thm_MeasureTheory_tendsto_ball_div_volume_of_tendsto_closedBall_div_volume
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

open MeasureTheory Filter
open scoped ENNReal Topology
open TeschlQM.Herglotz

theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∀ᵐ t ∂(volume : Measure ℝ), HasMeasureDeriv μ t (μ.rnDeriv volume t) := by
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv μ (volume : Measure ℝ)] with t ht
  exact MeasureTheory.tendsto_ball_div_volume_of_tendsto_closedBall_div_volume
    μ t (μ.rnDeriv volume t) ht
