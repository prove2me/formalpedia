-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.avoid_union_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:41:48.576878+00:00
-- url     : https://prove2.me/submissions/58a8e916-fb86-4d29-ac1e-be2adc0f19c8

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert_lower
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
include hx1
namespace QEC.Coding.ProbabilisticConstruction
theorem _root_.solution (T U : Finset I)
    (hc : ∀ A ⊆ U, ∀ i ∈ U, i ∉ A →
      μ.real (B i ∩ avoid B (T ∪ A)) ≤ x i * μ.real (avoid B (T ∪ A))) :
    (∏ i ∈ U, (1 - x i)) * μ.real (avoid B T) ≤ μ.real (avoid B (T ∪ U)) := by
  induction U using Finset.induction_on with
  | empty => simp
  | @insert i U hi ih =>
    have ih' := ih (fun A hA j hj hjA =>
      hc A (hA.trans (Finset.subset_insert _ _)) j (Finset.mem_insert_of_mem hj) hjA)
    have hs := avoid_insert_lower μ B hB x i (T ∪ U)
      (hc U (Finset.subset_insert _ _) i (Finset.mem_insert_self _ _) hi)
    rw [Finset.prod_insert hi]
    have hm := mul_le_mul_of_nonneg_left ih' (sub_nonneg.mpr (hx1 i).le)
    calc
      ((1 - x i) * ∏ j ∈ U, (1 - x j)) * μ.real (avoid B T)
          ≤ (1 - x i) * μ.real (avoid B (T ∪ U)) := by simpa [mul_assoc] using hm
      _ ≤ μ.real (avoid B (T ∪ insert i U)) := by
        simpa [Finset.union_insert] using hs
end QEC.Coding.ProbabilisticConstruction
