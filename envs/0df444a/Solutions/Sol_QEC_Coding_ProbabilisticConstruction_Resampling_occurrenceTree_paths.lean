-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.occurrenceTree_paths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:26:13.439667+00:00
-- url     : https://prove2.me/submissions/999ea2c5-1da4-42d2-af75-419572d1518c

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TreeProbability
import Mathlib.Data.Fintype.Fin
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_OccurrenceCounting
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPaths_pathsToTree


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open scoped BigOperators
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (R : Table (X := X)) (T : ℕ) (i : I)
    (n : occurrences vars bad R T i) :
    witnessPaths (supportGraph vars) (T + 1) i (occurrenceTree vars bad R T i n) =
      historyWitness (supportGraph vars) i (occurrenceHistory vars bad R n.val i
        (Finset.mem_filter.mp n.property).2) := by
  unfold occurrenceTree
  apply witnessPaths_pathsToTree
end QEC.Coding.ProbabilisticConstruction.Resampling
