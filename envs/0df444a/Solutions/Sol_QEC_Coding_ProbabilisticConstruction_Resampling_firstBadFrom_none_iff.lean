-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.firstBadFrom_none_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:41:13.294721+00:00
-- url     : https://prove2.me/submissions/0c96e314-db37-4349-bee9-076b2cf2bd4c

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Finset.Sort
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
variable {Ω I : Type*} (B : I → Set Ω) [∀ i, DecidablePred (· ∈ B i)]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (L : List I) (ω : Ω) :
    firstBadFrom B L ω = none ↔ ∀ i ∈ L, ω ∉ B i := by
  induction L with
  | nil => simp [firstBadFrom]
  | cons i L ih =>
    by_cases hi : ω ∈ B i <;> simp [firstBadFrom, hi, ih]
end QEC.Coding.ProbabilisticConstruction.Resampling
