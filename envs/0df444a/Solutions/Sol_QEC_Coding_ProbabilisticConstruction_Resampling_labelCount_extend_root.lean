-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.labelCount_extend_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:21:05.052209+00:00
-- url     : https://prove2.me/submissions/098e4b0b-3c37-4efe-b0f8-51e0d9f09929

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessTrees
import Mathlib.Data.Finset.Max
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_labelCount_insert
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPartition_zero
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.mem_closedNeighbors
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.witnessPartition_zero
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (root j : I) (P : Finset (List I)) (hroot : [] ∈ P) :
    labelCount root root (extendWitness G root j P) =
      labelCount root root P + if j = root then 1 else 0 := by
  by_cases h : (attachmentCandidates G root j P).Nonempty
  · exact labelCount_insert G root j root P h
  · have hne : j ≠ root := by
      intro he
      subst j
      apply h
      exact ⟨[], Finset.mem_filter.mpr ⟨hroot, by simp⟩⟩
    simp [extendWitness, h, hne]
end QEC.Coding.ProbabilisticConstruction.Resampling
