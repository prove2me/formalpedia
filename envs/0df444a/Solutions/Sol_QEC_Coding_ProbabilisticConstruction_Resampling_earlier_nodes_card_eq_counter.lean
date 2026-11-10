-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.earlier_nodes_card_eq_counter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:23:02.7298+00:00
-- url     : https://prove2.me/submissions/85adeeac-91e7-4ccb-b4e4-224c046c34d2

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessCompatibility
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryCounters
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_mem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_notMem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_nil_mem_witnessPaths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_timedHistoryWitness_earlier_variable
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_timedHistoryWitness_label
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_timedHistoryWitness_time_injective
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
      historyCounter vars root L p.2 v := by
  unfold historyCounter
  apply Finset.card_bij (fun q _ => q.2)
  · intro q hq
    obtain ⟨hqW, hqv, hqt⟩ := Finset.mem_filter.mp hq
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hqt, ?_⟩
    have he := timedHistoryWitness_label (supportGraph vars) root 0 L q hqW
    simpa only [Nat.sub_zero] using he ▸ hqv
  · intro q hq r hr he
    exact timedHistoryWitness_time_injective (supportGraph vars) root 0 L
      (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hr).1 he
  · intro k hk
    obtain ⟨hkr, hkv⟩ := Finset.mem_filter.mp hk
    obtain ⟨q, hq, hqk, hqv⟩ := timedHistoryWitness_earlier_variable vars root 0 L
      p hp v hpv k (Nat.zero_le _) (Finset.mem_range.mp hkr) (by simpa using hkv)
    exact ⟨q, Finset.mem_filter.mpr ⟨hq, hqv, by simpa [hqk] using hkr⟩, hqk⟩
end QEC.Coding.ProbabilisticConstruction.Resampling
