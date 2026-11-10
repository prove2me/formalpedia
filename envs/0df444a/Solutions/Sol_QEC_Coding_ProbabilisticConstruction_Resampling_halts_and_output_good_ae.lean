-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.halts_and_output_good_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:44:20.79251+00:00
-- url     : https://prove2.me/submissions/5e4f4c54-55b2-4696-a551-58862bb99e2c

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Expectation
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_halts_of_totalSteps_lt_top
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_output_good
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_totalSteps_finite_ae


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
variable [MeasurableSpace I] [MeasurableSingletonClass I]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
variable (hbad : ∀ i, MeasurableSet (bad i))
variable (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
variable (hcrit : ∀ i, eventProbability vars ν bad i ≤
  x i * ∏ j ∈ (supportGraph vars).neighborFinset i, (1 - x j))
include hbad hx0 hx1 hcrit
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution :
    ∀ᵐ R ∂tableLaw ν, Halts vars bad R ∧ ∀ i, output vars bad R ∉ localEvent vars bad i := by
  filter_upwards [totalSteps_finite_ae vars bad ν hbad x hx0 hx1 hcrit] with R hR
  have hh := halts_of_totalSteps_lt_top vars bad R hR
  exact ⟨hh, output_good vars bad R hh⟩
end QEC.Coding.ProbabilisticConstruction.Resampling
