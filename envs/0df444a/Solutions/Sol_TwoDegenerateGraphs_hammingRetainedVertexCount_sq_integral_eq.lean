-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingRetainedVertexCount_sq_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/2e75a7b0-f1b2-47e7-869f-b88bc36b2364

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_integrable
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_integral_eq_sum
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_real_event_eq_sum
import Theorems.Thm_TwoDegenerateGraphs_hammingRetainedVertexCount_sq

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension : ℕ) :
    (∫ retained,
      hammingRetainedVertexCount dimension retained ^ 2
        ∂hammingRetentionMeasure dimension) =
      hammingExpectedRetainedVertexSquare dimension := by
  classical
  simp_rw [hammingRetainedVertexCount_sq]
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun first _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        ∑ second : Bool × HammingWord dimension,
          if first ∈ retained ∧ second ∈ retained then (1 : ℝ) else 0))]
  unfold hammingExpectedRetainedVertexSquare
  apply Finset.sum_congr rfl
  intro first _
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun second _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        if first ∈ retained ∧ second ∈ retained then (1 : ℝ) else 0))]
  apply Finset.sum_congr rfl
  intro second _
  rw [hammingRetentionMeasure_integral_eq_sum,
    hammingRetentionMeasure_real_event_eq_sum]
  apply Finset.sum_congr rfl
  intro retained _
  by_cases hretained : first ∈ retained ∧ second ∈ retained <;>
    simp [hretained]
end TwoDegenerateGraphs
