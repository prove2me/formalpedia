-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.eventProbability_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:23:36.80234+00:00
-- url     : https://prove2.me/submissions/2c9eba58-09de-42d7-8ee1-275b05ee5868

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ExecutionWitness
import Mathlib.Data.ENNReal.BigOperators
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TreeProbability

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
variable (bad : ∀ i, Set (∀ v : vars i, X v))
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (i : I) : 0 ≤ eventProbability vars ν bad i :=
  ENNReal.toReal_nonneg
end QEC.Coding.ProbabilisticConstruction.Resampling
