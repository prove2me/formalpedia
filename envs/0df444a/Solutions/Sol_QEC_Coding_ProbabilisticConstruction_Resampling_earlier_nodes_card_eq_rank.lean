-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.earlier_nodes_card_eq_rank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:22:08.138435+00:00
-- url     : https://prove2.me/submissions/effcf03a-7820-4650-b1c3-0921ab6724e1

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessCompatibility
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryCounters
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_mem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_notMem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_nil_mem_witnessPaths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_timedHistoryWitness_depth_time
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_timedHistoryWitness_path_injective
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_timedHistoryWitness_paths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPartition_zero
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_mem
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_notMem
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.mem_closedNeighbors
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.nil_mem_witnessPaths
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.witnessPartition_zero
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
variable (vars : I → Finset V)
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (root : I) (L : List I) (p : List I × ℕ)
    (hp : p ∈ timedHistoryWitness (supportGraph vars) root 0 L)
    (v : V) (hpv : v ∈ vars (pathLabel root p.1)) :
    ((timedHistoryWitness (supportGraph vars) root 0 L).filter
      (fun q => v ∈ vars (pathLabel root q.1) ∧ q.2 < p.2)).card =
      variableRank vars root (historyWitness (supportGraph vars) root L) p.1 v := by
  unfold variableRank
  apply Finset.card_bij (fun q _ => q.1)
  · intro q hq
    obtain ⟨hqW, hqv, hqt⟩ := Finset.mem_filter.mp hq
    refine Finset.mem_filter.mpr ⟨?_, hqv, ?_⟩
    · rw [← timedHistoryWitness_paths (supportGraph vars) root 0 L]
      exact Finset.mem_image_of_mem Prod.fst hqW
    · exact (timedHistoryWitness_depth_time vars root 0 L q p hqW hp v hqv hpv).mp hqt
  · intro q hq r hr he
    exact timedHistoryWitness_path_injective (supportGraph vars) root 0 L
      (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hr).1 he
  · intro q hq
    obtain ⟨hqP, hqv, hqd⟩ := Finset.mem_filter.mp hq
    rw [← timedHistoryWitness_paths (supportGraph vars) root 0 L] at hqP
    obtain ⟨r, hr, he⟩ := Finset.mem_image.mp hqP
    have hrv : v ∈ vars (pathLabel root r.1) := he.symm ▸ hqv
    refine ⟨r, Finset.mem_filter.mpr ⟨hr, hrv, ?_⟩, he⟩
    apply (timedHistoryWitness_depth_time vars root 0 L r p hr hp v hrv hpv).mpr
    simpa [he] using hqd
end QEC.Coding.ProbabilisticConstruction.Resampling
