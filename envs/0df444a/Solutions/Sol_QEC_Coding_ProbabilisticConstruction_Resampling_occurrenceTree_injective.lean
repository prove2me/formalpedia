-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.occurrenceTree_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:35:03.753095+00:00
-- url     : https://prove2.me/submissions/964e98ec-8d52-458c-81da-9a546c8cfe4a

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TreeProbability
import Mathlib.Data.Fintype.Fin
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_OccurrenceCounting
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_prefixCount_strict
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_occurrenceHistory_count
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_occurrenceTree_paths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_historyWitness_root_count


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open scoped BigOperators
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (R : Table (X := X)) (T : ℕ) (i : I) :
    Function.Injective (occurrenceTree vars bad R T i) := by
  intro a b he
  have hp := congrArg (witnessPaths (supportGraph vars) (T + 1) i) he
  rw [occurrenceTree_paths, occurrenceTree_paths] at hp
  have hc := congrArg (labelCount i i) hp
  rw [historyWitness_root_count, historyWitness_root_count,
    occurrenceHistory_count, occurrenceHistory_count] at hc
  apply Subtype.ext
  rcases lt_trichotomy a.val b.val with hab | he | hba
  · have hh := prefixCount_strict vars bad R i a.val b.val hab
      (Finset.mem_filter.mp a.property).2
    omega
  · exact he
  · have hh := prefixCount_strict vars bad R i b.val a.val hba
      (Finset.mem_filter.mp b.property).2
    omega
end QEC.Coding.ProbabilisticConstruction.Resampling
