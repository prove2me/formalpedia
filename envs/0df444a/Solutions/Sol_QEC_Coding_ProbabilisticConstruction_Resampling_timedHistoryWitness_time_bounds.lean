-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.timedHistoryWitness_time_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:18:25.932232+00:00
-- url     : https://prove2.me/submissions/6b34d16d-c7a9-4021-b41b-2e0da0e915cb

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
theorem _root_.solution (root : I) (offset : ℕ) (L : List I)
    (p : List I × ℕ) (hp : p ∈ timedHistoryWitness G root offset L) :
    offset ≤ p.2 ∧ p.2 ≤ offset + L.length := by
  induction L generalizing offset with
  | nil =>
    have he : p = ([], offset) := by simpa [timedHistoryWitness] using hp
    simp [he]
  | cons j L ih =>
    simp only [timedHistoryWitness] at hp
    split_ifs at hp with h
    · rcases Finset.mem_insert.mp hp with he | hp
      · subst p; simp
      · have hb := ih (offset + 1) hp; simp only [List.length_cons]; omega
    · have hb := ih (offset + 1) hp; simp only [List.length_cons]; omega
end QEC.Coding.ProbabilisticConstruction.Resampling
