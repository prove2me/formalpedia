-- Prove2me | solution 1 for OWMR.slValue_mono_setup
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T01:17:47.471197+00:00
-- url     : https://prove2.me/submissions/8e13e4bb-3119-4066-91cf-83e4b1dd05c1

import Definitions.Def_owmr_single_location

open MeasureTheory
open scoped ENNReal NNReal
open OWMR

theorem solution (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (f : ℝ → ℝ) {K K' : ℝ}
    (hK : K ≤ K') : slValue ρ f K ≤ slValue ρ f K' := by
  unfold slValue
  refine iInf_mono fun U => iInf_mono fun _ => iInf_mono fun ν => iInf_mono fun _ =>
    iInf_mono fun q => iInf_mono fun _ => ?_
  unfold slAvgCost
  refine Filter.limsup_le_limsup (Filter.Eventually.of_forall fun T => ?_)
  dsimp only
  gcongr with ω t ht
  unfold slPeriodCost
  split_ifs <;> linarith
