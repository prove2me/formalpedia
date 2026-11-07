-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.measurableSet_localEvent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:09:08.139714+00:00
-- url     : https://prove2.me/submissions/571f16de-681e-42b8-bbd7-4f60f69c090c

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
namespace QEC.Coding.ProbabilisticConstruction
theorem _root_.solution (vars : I → Finset V)
    (bad : ∀ i, Set (∀ v : vars i, X v)) (hbad : ∀ i, MeasurableSet (bad i))
    (i : I) : MeasurableSet (localEvent vars bad i) :=
  (hbad i).preimage (vars i).measurable_restrict
end QEC.Coding.ProbabilisticConstruction
