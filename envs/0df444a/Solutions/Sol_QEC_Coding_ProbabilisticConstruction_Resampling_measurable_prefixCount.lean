-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.measurable_prefixCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:30:51.772709+00:00
-- url     : https://prove2.me/submissions/75428ac7-6fda-4b4b-a4bb-c3a5edab30b3

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_OccurrenceCounting
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Expectation
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_prefixCount_eq_indicator_sum
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_selected


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable [MeasurableSpace I] [MeasurableSingletonClass I]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (hbad : ∀ i, MeasurableSet (bad i)) (T : ℕ) (i : I) :
    Measurable (fun R : Table (X := X) => (prefixCount vars bad R T i : ℝ≥0∞)) := by
  classical
  simp_rw [prefixCount_eq_indicator_sum]
  apply Finset.measurable_sum
  intro n hn
  exact measurable_const.indicator
    ((measurable_selected vars bad hbad n) (measurableSet_singleton (some i)))
end QEC.Coding.ProbabilisticConstruction.Resampling
