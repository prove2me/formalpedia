-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.avoid_insert_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:41:05.379671+00:00
-- url     : https://prove2.me/submissions/89c85206-8152-4483-b836-0878a8798e75

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (B : I → Set Ω) (hB : ∀ i, MeasurableSet (B i))
variable (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
include hB
namespace QEC.Coding.ProbabilisticConstruction
theorem _root_.solution (i : I) (S : Finset I)
    (hc : μ.real (B i ∩ avoid B S) ≤ x i * μ.real (avoid B S)) :
    (1 - x i) * μ.real (avoid B S) ≤ μ.real (avoid B (insert i S)) := by
  have he := measureReal_inter_add_diff (μ := μ) (s := avoid B S) (hB i)
  rw [Set.inter_comm, ← avoid_insert] at he
  nlinarith
end QEC.Coding.ProbabilisticConstruction
