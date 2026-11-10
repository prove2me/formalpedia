-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.timedHistoryWitness_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:18:47.302218+00:00
-- url     : https://prove2.me/submissions/b2013f7e-11da-4d88-b5d4-ac3d76df3613

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
    ([], offset + L.length) ∈ timedHistoryWitness G root offset L := by
  induction L generalizing offset with
  | nil => simp [timedHistoryWitness]
  | cons j L ih =>
    have hh := ih (offset + 1)
    simp only [timedHistoryWitness]
    split_ifs with h
    · apply Finset.mem_insert_of_mem
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
    · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
end QEC.Coding.ProbabilisticConstruction.Resampling
