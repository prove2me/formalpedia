-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.firstBadFrom_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:41:17.66581+00:00
-- url     : https://prove2.me/submissions/48d36b19-7c55-44b7-8206-72453b27752e

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
theorem _root_.solution {L : List I} {ω : Ω} {i : I}
    (h : firstBadFrom B L ω = some i) : i ∈ L ∧ ω ∈ B i := by
  induction L with
  | nil => simp [firstBadFrom] at h
  | cons j L ih =>
    by_cases hj : ω ∈ B j
    · have he : j = i := by simpa [firstBadFrom, hj] using h
      subst j
      exact ⟨by simp, hj⟩
    · have ht : firstBadFrom B L ω = some i := by simpa [firstBadFrom, hj] using h
      obtain ⟨hiL, hi⟩ := ih ht
      exact ⟨List.mem_cons_of_mem _ hiL, hi⟩
end QEC.Coding.ProbabilisticConstruction.Resampling
