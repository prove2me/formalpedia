-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.select_some_bad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:42:15.042459+00:00
-- url     : https://prove2.me/submissions/e68db02c-9209-406e-9830-69638cbb48f0

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Finset.Sort
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_firstBadFrom_some

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
variable {Ω I : Type*} (B : I → Set Ω) [∀ i, DecidablePred (· ∈ B i)]
variable [Fintype I] [LinearOrder I]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution {ω : Ω} {i : I} (h : select B ω = some i) : ω ∈ B i :=
  (firstBadFrom_some B h).2
end QEC.Coding.ProbabilisticConstruction.Resampling
