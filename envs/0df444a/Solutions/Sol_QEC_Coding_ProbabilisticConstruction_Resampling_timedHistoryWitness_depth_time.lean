-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.timedHistoryWitness_depth_time
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:20:37.333202+00:00
-- url     : https://prove2.me/submissions/5f561e31-2589-4d63-a256-d117e556779d

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_timedHistoryWitness_time_bounds
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_candidate_of_shared_variable
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_newPath_deeper_than_candidate
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
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (vars : I → Finset V)
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (root : I) (offset : ℕ) (L : List I)
    (p q : List I × ℕ)
    (hp : p ∈ timedHistoryWitness (supportGraph vars) root offset L)
    (hq : q ∈ timedHistoryWitness (supportGraph vars) root offset L)
    (v : V) (hpv : v ∈ vars (pathLabel root p.1)) (hqv : v ∈ vars (pathLabel root q.1)) :
    p.2 < q.2 ↔ q.1.length < p.1.length := by
  induction L generalizing offset with
  | nil =>
    have he : p = ([], offset) := by simpa [timedHistoryWitness] using hp
    have hf : q = ([], offset) := by simpa [timedHistoryWitness] using hq
    simp [he, hf]
  | cons j L ih =>
    simp only [timedHistoryWitness] at hp hq
    split_ifs at hp hq with h
    · rcases Finset.mem_insert.mp hp with rfl | hp
      · rcases Finset.mem_insert.mp hq with rfl | hq
        · simp
        · have ht := (timedHistoryWitness_time_bounds (supportGraph vars) root
            (offset + 1) L q hq).1
          have hjv : v ∈ vars j := by simpa using hpv
          have hc := candidate_of_shared_variable vars root j _ q.1
            (Finset.mem_image_of_mem Prod.fst hq) v hjv hqv
          have hd := newPath_deeper_than_candidate (supportGraph vars) root j _ h q.1 hc
          constructor
          · intro _; exact hd
          · intro _; simp only [Prod.snd]; omega
      · rcases Finset.mem_insert.mp hq with rfl | hq
        · have ht := (timedHistoryWitness_time_bounds (supportGraph vars) root
            (offset + 1) L p hp).1
          have hjv : v ∈ vars j := by simpa using hqv
          have hc := candidate_of_shared_variable vars root j _ p.1
            (Finset.mem_image_of_mem Prod.fst hp) v hjv hpv
          have hd := newPath_deeper_than_candidate (supportGraph vars) root j _ h p.1 hc
          constructor <;> intro he <;> simp only [Prod.snd, Prod.fst] at he ⊢ <;> omega
        · exact ih (offset + 1) hp hq
    · exact ih (offset + 1) hp hq
end QEC.Coding.ProbabilisticConstruction.Resampling
