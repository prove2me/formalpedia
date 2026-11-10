-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.timedHistoryWitness_path_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:19:27.515849+00:00
-- url     : https://prove2.me/submissions/78fe274b-6dfb-4bbe-aa22-1689a324bafc

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_newPath_not_mem
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
    Set.InjOn Prod.fst (timedHistoryWitness G root offset L : Set (List I × ℕ)) := by
  induction L generalizing offset with
  | nil => simp [timedHistoryWitness, Set.InjOn]
  | cons j L ih =>
    intro a ha b hb he
    simp only [timedHistoryWitness] at ha hb
    split_ifs at ha hb with h
    · have hn := newPath_not_mem G root j
        ((timedHistoryWitness G root (offset + 1) L).image Prod.fst) h
      rcases Finset.mem_insert.mp ha with rfl | ha
      · rcases Finset.mem_insert.mp hb with rfl | hb
        · rfl
        · apply False.elim
          apply hn
          have hm := Finset.mem_image_of_mem Prod.fst hb
          simpa only [← he] using hm
      · rcases Finset.mem_insert.mp hb with rfl | hb
        · apply False.elim
          apply hn
          have hm := Finset.mem_image_of_mem Prod.fst ha
          simpa only [he] using hm
        · exact ih (offset + 1) ha hb he
    · exact ih (offset + 1) ha hb he
end QEC.Coding.ProbabilisticConstruction.Resampling
