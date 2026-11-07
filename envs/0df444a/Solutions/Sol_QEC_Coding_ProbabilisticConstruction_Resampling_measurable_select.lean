-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.measurable_select
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:42:26.27117+00:00
-- url     : https://prove2.me/submissions/478feb0c-e85e-45b1-a0f7-d66d8efc2ce9

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Finset.Sort
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_firstBadFrom

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
variable {Ω I : Type*} (B : I → Set Ω) [∀ i, DecidablePred (· ∈ B i)]
variable [Fintype I] [LinearOrder I]
variable [MeasurableSpace Ω] [MeasurableSpace I]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (hB : ∀ i, MeasurableSet (B i)) : Measurable (select B) :=
  measurable_firstBadFrom B hB _
end QEC.Coding.ProbabilisticConstruction.Resampling
