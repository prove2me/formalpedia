-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.prefixCount_monotone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:26:10.883968+00:00
-- url     : https://prove2.me/submissions/f3f5cd50-bdfd-49a7-b3a1-3f04b89e3455

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TreeProbability
import Mathlib.Data.Fintype.Fin
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_OccurrenceCounting

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open scoped BigOperators
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (R : Table (X := X)) (i : I) :
    Monotone (fun T => prefixCount vars bad R T i) := by
  intro a b hab
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hab))
end QEC.Coding.ProbabilisticConstruction.Resampling
