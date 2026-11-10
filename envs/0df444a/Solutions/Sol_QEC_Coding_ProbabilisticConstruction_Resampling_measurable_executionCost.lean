-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.measurable_executionCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:36:55.709885+00:00
-- url     : https://prove2.me/submissions/e4bb37a9-2fce-48ff-b92f-54764ffaa2e6

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Cost
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_executionScanCost
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_executionRefreshCost
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurableSet_halts
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_haltTime


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
include hbad
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (queryCost : I → ℝ≥0∞) (sampleCost : V → ℝ≥0∞)
    (outputCost : ℝ≥0∞) :
    Measurable (executionCost vars bad queryCost sampleCost outputCost (X := X)) := by
  have hscan : Measurable (fun z : Table (X := X) × ℕ =>
      ∑ n ∈ Finset.range (z.2 + 1), executionScanCost vars bad queryCost z.1 n) :=
    measurable_from_prod_countable_left (fun N => Finset.measurable_sum (Finset.range (N + 1))
      (fun n _ => measurable_executionScanCost vars bad hbad queryCost n))
  have hrefresh : Measurable (fun z : Table (X := X) × ℕ =>
      ∑ n ∈ Finset.range z.2, executionRefreshCost vars bad sampleCost z.1 n) :=
    measurable_from_prod_countable_left (fun N => Finset.measurable_sum (Finset.range N)
      (fun n _ => measurable_executionRefreshCost vars bad hbad sampleCost n))
  have ht := measurable_id.prodMk (measurable_haltTime vars bad hbad)
  exact Measurable.ite (measurableSet_halts vars bad hbad)
    ((measurable_const.add (hscan.comp ht)).add (hrefresh.comp ht)) measurable_const
end QEC.Coding.ProbabilisticConstruction.Resampling
