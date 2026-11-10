-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.occurrenceHistory_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:30:54.40321+00:00
-- url     : https://prove2.me/submissions/1dff81fb-6fd1-4995-861e-33191bd934ed

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TreeProbability
import Mathlib.Data.Fintype.Fin
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_OccurrenceCounting
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_list_count_eq_history_count
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_occurrenceHistory_length
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_occurrenceHistory_matches
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.occurrenceHistory_length



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open scoped BigOperators
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (R : Table (X := X)) (n : ℕ) (i : I)
    (hi : selected vars bad R n = some i) :
    (occurrenceHistory vars bad R n i hi).count i = prefixCount vars bad R n i := by
  rw [list_count_eq_history_count i i, occurrenceHistory_length]
  unfold prefixCount occurrences
  congr 1
  apply Finset.filter_congr
  intro k hk
  have he := occurrenceHistory_matches vars bad R n i hi k (Finset.mem_range.mp hk).le
  rw [he, Option.some.injEq]
end QEC.Coding.ProbabilisticConstruction.Resampling
