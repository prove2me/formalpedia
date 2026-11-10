-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.measurable_scanCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:30:00.979022+00:00
-- url     : https://prove2.me/submissions/a55e45f4-4740-4626-a4d7-89cb182a9440

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Cost

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
variable {Ω I : Type*} (B : I → Set Ω) [∀ i, DecidablePred (· ∈ B i)]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution [MeasurableSpace Ω] (hB : ∀ i, MeasurableSet (B i))
    (queryCost : I → ℝ≥0∞) (L : List I) : Measurable (scanCost B queryCost L) := by
  induction L with
  | nil => exact measurable_const
  | cons i L ih => exact measurable_const.add (Measurable.ite (hB i) measurable_const ih)
end QEC.Coding.ProbabilisticConstruction.Resampling
