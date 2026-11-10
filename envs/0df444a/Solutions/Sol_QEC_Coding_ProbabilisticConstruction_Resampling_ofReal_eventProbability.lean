-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.ofReal_eventProbability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:24:22.820017+00:00
-- url     : https://prove2.me/submissions/7a4a5af7-92bf-4517-8bcd-137a0107cbd6

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
theorem _root_.solution (i : I) :
    ENNReal.ofReal (eventProbability vars ν bad i) =
      (Measure.pi ν) (localEvent vars bad i) :=
  ENNReal.ofReal_toReal (measure_ne_top _ _)
end QEC.Coding.ProbabilisticConstruction.Resampling
