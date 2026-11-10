-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.witnessPaths_pathsToTree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:20:40.803342+00:00
-- url     : https://prove2.me/submissions/7eb3f551-27a5-4aa0-b0e2-44c592000c81

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessTrees
import Mathlib.Data.Finset.Max
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_nil_mem_witnessPaths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_cons_mem_witnessPaths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPartition_zero
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.mem_closedNeighbors
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.witnessPartition_zero
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert


attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.nil_mem_witnessPaths

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (h : ℕ) (root : I) (P : Finset (List I))
    (hP : ProperPaths G root P) (hd : ∀ p ∈ P, p.length < h) :
    witnessPaths G h root (pathsToTree G h root P hP hd) = P := by
  induction h generalizing root P with
  | zero => exact False.elim (Nat.not_lt_zero _ (hd [] hP.1))
  | succ h ih =>
    ext p
    cases p with
    | nil => simp only [nil_mem_witnessPaths, true_iff]; exact hP.1
    | cons j p =>
      rw [cons_mem_witnessPaths]
      constructor
      · rintro ⟨hj, child, hc, hp⟩
        change (if he : [j] ∈ P then some
          (pathsToTree G h j (childPaths P j) (ProperPaths.child G hP he) (childPaths_depth P j h hd))
          else none) = some child at hc
        split_ifs at hc with he
        · have hc' := Option.some.inj hc
          subst child
          rw [ih] at hp
          exact (mem_childPaths P j p).mp hp
      · intro hp
        have hjP : [j] ∈ P := by
          have hprefix : ∀ q : List I, j :: q ∈ P → [j] ∈ P := by
            intro q
            induction q using List.reverseRecOn with
            | nil => exact id
            | append_singleton q k ihq =>
              intro hh
              apply ihq
              exact (hP.2 (j :: q) k (by simpa using hh)).1
          exact hprefix p hp
        have hj : j ∈ closedNeighbors G root := by
          simpa using (hP.2 [] j hjP).2
        refine ⟨hj, pathsToTree G h j (childPaths P j) (ProperPaths.child G hP hjP)
          (childPaths_depth P j h hd), ?_, ?_⟩
        · simp [pathsToTree, hjP]
        · rw [ih]
          exact (mem_childPaths P j p).mpr hp
end QEC.Coding.ProbabilisticConstruction.Resampling
