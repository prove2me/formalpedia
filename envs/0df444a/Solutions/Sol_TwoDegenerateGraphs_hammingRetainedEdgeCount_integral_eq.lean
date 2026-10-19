-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingRetainedEdgeCount_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/07c54c92-d8f6-4107-8d1b-0827beb41845

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_integrable
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_integral_eq_sum
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_real_event_eq_sum

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension radius : ℕ) :
    (∫ retained,
      hammingRetainedEdgeCount dimension radius retained
        ∂hammingRetentionMeasure dimension) =
      hammingExpectedRetainedEdgeCount dimension radius := by
  classical
  unfold hammingRetainedEdgeCount hammingExpectedRetainedEdgeCount
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun left _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        ∑ right : HammingWord dimension,
          if hammingDist left right ≤ radius ∧
              (false, left) ∈ retained ∧ (true, right) ∈ retained
          then (1 : ℝ) else 0))]
  apply Finset.sum_congr rfl
  intro left _
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun right _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        if hammingDist left right ≤ radius ∧
            (false, left) ∈ retained ∧ (true, right) ∈ retained
        then (1 : ℝ) else 0))]
  apply Finset.sum_congr rfl
  intro right _
  by_cases hedge : hammingDist left right ≤ radius
  · simp only [hedge, true_and, if_true]
    rw [hammingRetentionMeasure_integral_eq_sum,
      hammingRetentionMeasure_real_event_eq_sum]
    apply Finset.sum_congr rfl
    intro retained _
    by_cases hretained :
        (false, left) ∈ retained ∧ (true, right) ∈ retained <;>
      simp [hretained]
  · simp [hedge]
end TwoDegenerateGraphs
