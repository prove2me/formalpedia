-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.product_localLemma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:51:11.325612+00:00
-- url     : https://prove2.me/submissions/9a96a2ce-c822-49e7-bdb4-cb760e39905d

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_localLemma_conditional
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_localLemma_product_lower
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_localLemma_positive
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_localLemma_exists
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_measurableSet_localEvent
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_product_hasDependencyGraph

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
namespace QEC.Coding.ProbabilisticConstruction
theorem _root_.solution (ν : ∀ v, Measure (X v))
    [∀ v, IsProbabilityMeasure (ν v)] (vars : I → Finset V)
    (bad : ∀ i, Set (∀ v : vars i, X v)) (hbad : ∀ i, MeasurableSet (bad i))
    (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hcrit : ∀ i, (Measure.pi ν).real (localEvent vars bad i) ≤
      x i * ∏ j ∈ (supportGraph vars).neighborFinset i, (1 - x j)) :
    (∀ S, (∏ i ∈ S, (1 - x i)) ≤ (Measure.pi ν).real (avoid (localEvent vars bad) S)) ∧
    (∀ S, 0 < (Measure.pi ν).real (avoid (localEvent vars bad) S)) ∧
    (∀ S i, i ∉ S → (Measure.pi ν).real (localEvent vars bad i ∩
      avoid (localEvent vars bad) S) ≤ x i * (Measure.pi ν).real
        (avoid (localEvent vars bad) S)) ∧
    (∃ ω, ∀ i, ω ∉ localEvent vars bad i) := by
  have hd := product_hasDependencyGraph ν vars bad hbad
  have hm := measurableSet_localEvent vars bad hbad
  exact ⟨localLemma_product_lower _ _ hm x hx0 hx1 _ hd hcrit,
    localLemma_positive _ _ hm x hx0 hx1 _ hd hcrit,
    localLemma_conditional _ _ hm x hx0 hx1 _ hd hcrit,
    localLemma_exists _ _ hm x hx0 hx1 _ hd hcrit⟩
end QEC.Coding.ProbabilisticConstruction
