-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.localLemma_product_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:43:30.976543+00:00
-- url     : https://prove2.me/submissions/32fd3dc5-e415-41e5-aa27-423313ebc150

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_union_lower
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_localLemma_conditional
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
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
variable (G : SimpleGraph I) [DecidableRel G.Adj]
variable (hdep : HasDependencyGraph μ B G)
variable (hcrit : ∀ i, μ.real (B i) ≤ x i * ∏ j ∈ G.neighborFinset i, (1 - x j))
include hx0 hx1 hdep hcrit
namespace QEC.Coding.ProbabilisticConstruction
theorem _root_.solution (S : Finset I) :
    (∏ i ∈ S, (1 - x i)) ≤ μ.real (avoid B S) := by
  have h := avoid_union_lower μ B hB x hx1 ∅ S (by
    intro A hA i hi hiA
    simpa using localLemma_conditional μ B hB x hx0 hx1 G hdep hcrit A i hiA)
  simpa using h
end QEC.Coding.ProbabilisticConstruction
