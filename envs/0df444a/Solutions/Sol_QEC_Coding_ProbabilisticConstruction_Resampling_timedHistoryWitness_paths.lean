-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.timedHistoryWitness_paths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:18:38.817994+00:00
-- url     : https://prove2.me/submissions/4ab4984b-2e04-4099-b4e3-6e08a4c49f4f

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_nil_mem_witnessPaths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPartition_zero
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.mem_closedNeighbors
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.nil_mem_witnessPaths
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.witnessPartition_zero
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (root : I) (offset : ℕ) (L : List I) :
    (timedHistoryWitness G root offset L).image Prod.fst = historyWitness G root L := by
  induction L generalizing offset with
  | nil => simp [timedHistoryWitness, historyWitness]
  | cons j L ih =>
    simp only [timedHistoryWitness, historyWitness, extendWitness]
    rw [ih]
    split_ifs <;> simp [Finset.image_insert, ih]
end QEC.Coding.ProbabilisticConstruction.Resampling
