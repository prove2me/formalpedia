-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.timedHistoryWitness_earlier_variable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:20:43.9692+00:00
-- url     : https://prove2.me/submissions/4ce56c33-fd5d-4872-a058-0ec2821e6376

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_candidate_of_shared_variable
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
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (vars : I → Finset V)
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (root : I) (offset : ℕ) (L : List I)
    (p : List I × ℕ) (hp : p ∈ timedHistoryWitness (supportGraph vars) root offset L)
    (v : V) (hpv : v ∈ vars (pathLabel root p.1)) (k : ℕ)
    (hk : offset ≤ k) (hkp : k < p.2)
    (hkv : v ∈ vars (historyLabel root L (k - offset))) :
    ∃ q ∈ timedHistoryWitness (supportGraph vars) root offset L,
      q.2 = k ∧ v ∈ vars (pathLabel root q.1) := by
  induction L generalizing offset with
  | nil =>
    have he : p = ([], offset) := by simpa [timedHistoryWitness] using hp
    simp only [he, Prod.snd] at hkp
    omega
  | cons j L ih =>
    simp only [timedHistoryWitness] at hp ⊢
    split_ifs at hp ⊢ with h
    · rcases Finset.mem_insert.mp hp with rfl | hp
      · simp only [Prod.snd] at hkp; omega
      · by_cases he : k = offset
        · subst k
          have hjv : v ∈ vars j := by simpa [historyLabel] using hkv
          refine ⟨_, Finset.mem_insert_self _ _, rfl, ?_⟩
          simpa using hjv
        · have hk' : offset + 1 ≤ k := by omega
          have hd : k - offset = (k - (offset + 1)) + 1 := by omega
          have hv' : v ∈ vars (historyLabel root L (k - (offset + 1))) := by
            simpa [historyLabel, hd] using hkv
          obtain ⟨q, hq, hqk, hqv⟩ := ih (offset + 1) hp hk' hv'
          exact ⟨q, Finset.mem_insert_of_mem hq, hqk, hqv⟩
    · by_cases he : k = offset
      · subst k
        have hjv : v ∈ vars j := by simpa [historyLabel] using hkv
        exact False.elim (h ⟨p.1, candidate_of_shared_variable vars root j _ p.1
          (Finset.mem_image_of_mem Prod.fst hp) v hjv hpv⟩)
      · have hk' : offset + 1 ≤ k := by omega
        have hd : k - offset = (k - (offset + 1)) + 1 := by omega
        have hv' : v ∈ vars (historyLabel root L (k - (offset + 1))) := by
          simpa [historyLabel, hd] using hkv
        exact ih (offset + 1) hp hk' hv'
end QEC.Coding.ProbabilisticConstruction.Resampling
