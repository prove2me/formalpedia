-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.refreshed_columns_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:51:22.390609+00:00
-- url     : https://prove2.me/submissions/a33ca499-f4b1-4e81-b4e9-ac85f1acda7d

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Finset.Sort
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_counters_monotone
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_resampled_read_fresh

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
variable {X : V → Type*}
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (R : Table (X := X)) (n m : ℕ) (hnm : n < m)
    (i : I) (hm : selected vars bad R m = some i) {v : V} (hv : v ∈ vars i) :
    counters vars bad R (n + 1) v < counters vars bad R (m + 1) v :=
  lt_of_le_of_lt (counters_monotone vars bad R v (Nat.succ_le_of_lt hnm))
    (resampled_read_fresh vars bad R m i hm hv)
end QEC.Coding.ProbabilisticConstruction.Resampling
