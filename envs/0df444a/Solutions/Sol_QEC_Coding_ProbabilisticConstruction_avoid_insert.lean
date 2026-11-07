-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.avoid_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:09:17.630647+00:00
-- url     : https://prove2.me/submissions/6386b1f2-1440-422c-8b89-2908ed1bcc61

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
namespace QEC.Coding.ProbabilisticConstruction
theorem _root_.solution (B : I → Set Ω) (i : I) (S : Finset I) :
    avoid B (insert i S) = avoid B S \ B i := by
  ext ω
  simp only [avoid, Set.mem_setOf_eq, Finset.mem_insert, forall_eq_or_imp,
    Set.mem_diff]
  tauto
end QEC.Coding.ProbabilisticConstruction
