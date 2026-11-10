-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.occurrenceTree_compatible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:31:45.584192+00:00
-- url     : https://prove2.me/submissions/867f2c15-3f55-402c-bff0-25fc13549a56

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TreeProbability
import Mathlib.Data.Fintype.Fin
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_OccurrenceCounting
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_occurrenceTree_paths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_occurrenceHistory_compatible


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
    R ∈ compatible vars bad i
      (witnessPaths (supportGraph vars) (T + 1) i (occurrenceTree vars bad R T i n)) := by
  rw [occurrenceTree_paths]
  exact occurrenceHistory_compatible vars bad R n.val i _
end QEC.Coding.ProbabilisticConstruction.Resampling
