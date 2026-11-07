-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.measurableSet_avoid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:51:02.901799+00:00
-- url     : https://prove2.me/submissions/1cd4295e-e6c9-4a09-ac47-b4c3c4e699ed

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
namespace QEC.Coding.ProbabilisticConstruction
theorem _root_.solution (B : I → Set Ω) (hB : ∀ i, MeasurableSet (B i))
    (S : Finset I) : MeasurableSet (avoid B S) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => rw [avoid_insert]; exact ih.diff (hB i)
end QEC.Coding.ProbabilisticConstruction
