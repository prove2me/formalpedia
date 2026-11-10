-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.expected_totalCount_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:40:01.791626+00:00
-- url     : https://prove2.me/submissions/625b66a1-0342-4c4b-b4d8-6b844874a0be

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_OccurrenceCounting
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Expectation
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_prefixCount
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_expected_prefixCount_le
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_prefixCount_monotone


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable [MeasurableSpace I] [MeasurableSingletonClass I]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
variable (hbad : ∀ i, MeasurableSet (bad i))
variable (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
variable (hcrit : ∀ i, eventProbability vars ν bad i ≤
  x i * ∏ j ∈ (supportGraph vars).neighborFinset i, (1 - x j))
include hbad hx0 hx1 hcrit
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (i : I) :
    (∫⁻ R, totalCount vars bad R i ∂tableLaw ν) ≤ ENNReal.ofReal (resamplingBudget x i) := by
  unfold totalCount
  rw [lintegral_iSup (fun T => measurable_prefixCount vars bad hbad T i)]
  · exact iSup_le (fun T => expected_prefixCount_le vars bad ν hbad x hx0 hx1 hcrit T i)
  · intro a b hab R
    exact (Nat.cast_le (α := ℝ≥0∞)).mpr (prefixCount_monotone vars bad R i hab)
end QEC.Coding.ProbabilisticConstruction.Resampling
