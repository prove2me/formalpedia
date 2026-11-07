-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.measurable_firstBadFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:41:29.339711+00:00
-- url     : https://prove2.me/submissions/ea7a5f3c-8535-4b0b-953b-a0bed32d1d2e

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Finset.Sort
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
variable {Ω I : Type*} (B : I → Set Ω) [∀ i, DecidablePred (· ∈ B i)]
variable [Fintype I] [LinearOrder I]
variable [MeasurableSpace Ω] [MeasurableSpace I]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (hB : ∀ i, MeasurableSet (B i)) (L : List I) :
    Measurable (firstBadFrom B L) := by
  induction L with
  | nil => exact measurable_const
  | cons i L ih => exact Measurable.ite (hB i) measurable_const ih
end QEC.Coding.ProbabilisticConstruction.Resampling
