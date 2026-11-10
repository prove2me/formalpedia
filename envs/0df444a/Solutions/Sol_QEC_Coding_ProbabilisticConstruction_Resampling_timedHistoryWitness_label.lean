-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.timedHistoryWitness_label
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:19:46.222888+00:00
-- url     : https://prove2.me/submissions/9bc234a4-0261-4c91-83fc-cf1e5fdbd77e

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_timedHistoryWitness_time_bounds
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
theorem _root_.solution (root : I) (offset : ℕ) (L : List I)
    (p : List I × ℕ) (hp : p ∈ timedHistoryWitness G root offset L) :
    pathLabel root p.1 = historyLabel root L (p.2 - offset) := by
  induction L generalizing offset with
  | nil =>
    have he : p = ([], offset) := by simpa [timedHistoryWitness] using hp
    simp [he, historyLabel]
  | cons j L ih =>
    simp only [timedHistoryWitness] at hp
    split_ifs at hp with h
    · rcases Finset.mem_insert.mp hp with rfl | hp
      · simp [historyLabel]
      · have hb := (timedHistoryWitness_time_bounds G root (offset + 1) L p hp).1
        have he : p.2 - offset = (p.2 - (offset + 1)) + 1 := by omega
        simpa [historyLabel, he] using ih (offset + 1) hp
    · have hb := (timedHistoryWitness_time_bounds G root (offset + 1) L p hp).1
      have he : p.2 - offset = (p.2 - (offset + 1)) + 1 := by omega
      simpa [historyLabel, he] using ih (offset + 1) hp
end QEC.Coding.ProbabilisticConstruction.Resampling
