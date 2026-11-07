-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.select_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:51:12.361666+00:00
-- url     : https://prove2.me/submissions/0e1609cb-8b15-4ace-9480-2690f661d47d

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Finset.Sort
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_firstBadFrom_le
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
variable {Ω I : Type*} (B : I → Set Ω) [∀ i, DecidablePred (· ∈ B i)]
variable [Fintype I] [LinearOrder I]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution {ω : Ω} {i j : I} (hi : select B ω = some i)
    (hj : ω ∈ B j) : i ≤ j :=
  firstBadFrom_le B (Finset.pairwise_sort _ _) hi (by simp) hj
end QEC.Coding.ProbabilisticConstruction.Resampling
