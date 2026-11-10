-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.labelCount_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:19:24.429398+00:00
-- url     : https://prove2.me/submissions/99cea93b-3e84-42b8-962c-30fb0708e7f2

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessTrees
import Mathlib.Data.Finset.Max
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_newPath_not_mem
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
theorem _root_.solution (root j k : I) (P : Finset (List I))
    (h : (attachmentCandidates G root j P).Nonempty) :
    labelCount root k (extendWitness G root j P) =
      labelCount root k P + if j = k then 1 else 0 := by
  have hn := newPath_not_mem G root j P h
  simp only [extendWitness, dif_pos h, labelCount, Finset.filter_insert,
    pathLabel_append_singleton]
  split_ifs with hj
  · rw [Finset.card_insert_of_notMem (fun hm => hn (Finset.mem_filter.mp hm).1)]
  · simp
end QEC.Coding.ProbabilisticConstruction.Resampling
