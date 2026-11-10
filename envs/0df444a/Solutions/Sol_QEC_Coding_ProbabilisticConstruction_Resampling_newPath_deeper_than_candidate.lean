-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.newPath_deeper_than_candidate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:17:30.815899+00:00
-- url     : https://prove2.me/submissions/8110df3f-3c1a-4440-8e98-753e275998c3

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
    (h : (attachmentCandidates G root j P).Nonempty) (q : List I)
    (hq : q ∈ attachmentCandidates G root j P) :
    q.length < (attachmentParent G root j P h ++ [j]).length := by
  have hd := (attachmentParent_spec G root j P h).2 q hq
  simp only [List.length_append, List.length_singleton]
  omega
end QEC.Coding.ProbabilisticConstruction.Resampling
