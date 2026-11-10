-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.newPath_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:17:18.724716+00:00
-- url     : https://prove2.me/submissions/4dcf991a-fdbb-47f0-9685-f587349d5a96

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessTrees
import Mathlib.Data.Finset.Max
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
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
theorem _root_.solution (root j : I) (P : Finset (List I))
    (h : (attachmentCandidates G root j P).Nonempty) :
    attachmentParent G root j P h ++ [j] ∉ P := by
  intro hm
  have hc : attachmentParent G root j P h ++ [j] ∈ attachmentCandidates G root j P := by
    apply Finset.mem_filter.mpr
    exact ⟨hm, by simp⟩
  have hd := (attachmentParent_spec G root j P h).2 _ hc
  simp only [List.length_append, List.length_singleton] at hd
  omega
end QEC.Coding.ProbabilisticConstruction.Resampling
