-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.localLemma_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:44:49.685204+00:00
-- url     : https://prove2.me/submissions/19258965-4ed4-4b89-a82f-20df9ba952ea

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_localLemma_positive

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
theorem _root_.solution : ∃ ω, ∀ i, ω ∉ B i := by
  obtain ⟨ω, hω⟩ := nonempty_of_measureReal_ne_zero
    (localLemma_positive μ B hB x hx0 hx1 G hdep hcrit Finset.univ).ne'
  exact ⟨ω, fun i => hω i (Finset.mem_univ _)⟩
end QEC.Coding.ProbabilisticConstruction
