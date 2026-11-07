-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.measurable_familyRead
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:42:04.474201+00:00
-- url     : https://prove2.me/submissions/9d765466-679b-4981-b004-95a24e109148

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
import Mathlib.Probability.Independence.InfinitePi
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (coords : A → Finset V) (column : ∀ a, coords a → ℕ) :
    Measurable (familyRead (X := X) coords column) := by
  apply measurable_pi_lambda
  intro a
  exact measurable_pi_lambda _ (fun v => measurable_pi_apply (v.val, column a v))
end QEC.Coding.ProbabilisticConstruction.Resampling
