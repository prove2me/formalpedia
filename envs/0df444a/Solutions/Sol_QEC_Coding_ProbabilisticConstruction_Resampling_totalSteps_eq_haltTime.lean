-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.totalSteps_eq_haltTime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:35:06.301242+00:00
-- url     : https://prove2.me/submissions/0cd225e6-fb4a-4b5e-b8fc-6d72a4c00815

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Expectation
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_sum_prefixCount_eq
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_haltTime_spec
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_active_before_haltTime
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_totalCount_eq_at_halt

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (R : Table (X := X)) (h : Halts vars bad R) :
    totalSteps vars bad R = (haltTime vars bad R : ℝ≥0∞) := by
  unfold totalSteps
  simp_rw [totalCount_eq_at_halt vars bad R _ (haltTime_spec vars bad R h)]
  exact_mod_cast sum_prefixCount_eq vars bad R (haltTime vars bad R)
    (active_before_haltTime vars bad R h)
end QEC.Coding.ProbabilisticConstruction.Resampling
