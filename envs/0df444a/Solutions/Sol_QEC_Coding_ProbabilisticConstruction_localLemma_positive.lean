-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.localLemma_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:44:16.767283+00:00
-- url     : https://prove2.me/submissions/0b11dbb5-4cf5-424e-a2af-0f54c73de163

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_localLemma_product_lower

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
theorem _root_.solution (S : Finset I) : 0 < μ.real (avoid B S) :=
  lt_of_lt_of_le (Finset.prod_pos (fun i _ => sub_pos.mpr (hx1 i)))
    (localLemma_product_lower μ B hB x hx0 hx1 G hdep hcrit S)
end QEC.Coding.ProbabilisticConstruction
