-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingRetainedEdgeCount_sq_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/9ae8f453-2495-4d53-96dc-c539de5f6d10

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_integrable
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_integral_eq_sum
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_real_event_eq_sum
import Theorems.Thm_TwoDegenerateGraphs_hammingRetainedEdgeCount_sq

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension radius : ℕ) :
    (∫ retained,
      hammingRetainedEdgeCount dimension radius retained ^ 2
        ∂hammingRetentionMeasure dimension) =
      hammingExpectedRetainedEdgeSquare dimension radius := by
  classical
  simp_rw [hammingRetainedEdgeCount_sq]
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun firstLeft _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        ∑ firstRight : HammingWord dimension,
          ∑ secondLeft : HammingWord dimension,
            ∑ secondRight : HammingWord dimension,
              if hammingDist firstLeft firstRight ≤ radius ∧
                  hammingDist secondLeft secondRight ≤ radius then
                if (false, firstLeft) ∈ retained ∧
                    (true, firstRight) ∈ retained ∧
                    (false, secondLeft) ∈ retained ∧
                    (true, secondRight) ∈ retained
                then (1 : ℝ) else 0
              else 0))]
  unfold hammingExpectedRetainedEdgeSquare
  apply Finset.sum_congr rfl
  intro firstLeft _
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun firstRight _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        ∑ secondLeft : HammingWord dimension,
          ∑ secondRight : HammingWord dimension,
            if hammingDist firstLeft firstRight ≤ radius ∧
                hammingDist secondLeft secondRight ≤ radius then
              if (false, firstLeft) ∈ retained ∧
                  (true, firstRight) ∈ retained ∧
                  (false, secondLeft) ∈ retained ∧
                  (true, secondRight) ∈ retained
              then (1 : ℝ) else 0
            else 0))]
  apply Finset.sum_congr rfl
  intro firstRight _
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun secondLeft _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        ∑ secondRight : HammingWord dimension,
          if hammingDist firstLeft firstRight ≤ radius ∧
              hammingDist secondLeft secondRight ≤ radius then
            if (false, firstLeft) ∈ retained ∧
                (true, firstRight) ∈ retained ∧
                (false, secondLeft) ∈ retained ∧
                (true, secondRight) ∈ retained
            then (1 : ℝ) else 0
          else 0))]
  apply Finset.sum_congr rfl
  intro secondLeft _
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun secondRight _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        if hammingDist firstLeft firstRight ≤ radius ∧
            hammingDist secondLeft secondRight ≤ radius then
          if (false, firstLeft) ∈ retained ∧
              (true, firstRight) ∈ retained ∧
              (false, secondLeft) ∈ retained ∧
              (true, secondRight) ∈ retained
          then (1 : ℝ) else 0
        else 0))]
  apply Finset.sum_congr rfl
  intro secondRight _
  by_cases hedge :
      hammingDist firstLeft firstRight ≤ radius ∧
        hammingDist secondLeft secondRight ≤ radius
  · simp only [hedge]
    rw [hammingRetentionMeasure_integral_eq_sum,
      hammingRetentionMeasure_real_event_eq_sum]
    apply Finset.sum_congr rfl
    intro retained _
    by_cases hretained :
        (false, firstLeft) ∈ retained ∧
          (true, firstRight) ∈ retained ∧
          (false, secondLeft) ∈ retained ∧
          (true, secondRight) ∈ retained <;>
      simp [hretained]
  · simp [hedge]
end TwoDegenerateGraphs
