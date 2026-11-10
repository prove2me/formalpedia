-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.candidate_of_shared_variable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:18:29.036342+00:00
-- url     : https://prove2.me/submissions/494927f1-bb1c-4b88-bc7f-730e670c3f45

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.mem_closedNeighbors



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (vars : I → Finset V)
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (root j : I) (P : Finset (List I))
    (p : List I) (hp : p ∈ P) (v : V) (hj : v ∈ vars j)
    (hv : v ∈ vars (pathLabel root p)) :
    p ∈ attachmentCandidates (supportGraph vars) root j P := by
  apply Finset.mem_filter.mpr
  refine ⟨hp, ?_⟩
  rw [mem_closedNeighbors]
  by_cases he : j = pathLabel root p
  · exact Or.inl he
  · exact Or.inr ⟨Ne.symm he, fun hd => Finset.disjoint_left.mp hd hv hj⟩
end QEC.Coding.ProbabilisticConstruction.Resampling
