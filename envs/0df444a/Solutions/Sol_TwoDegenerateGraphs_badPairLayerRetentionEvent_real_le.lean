-- Prove2me | solution 1 for TwoDegenerateGraphs.badPairLayerRetentionEvent_real_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/87e8d815-f164-45f0-86c9-bccd1e9e0a22

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_badPairChildRetentionEvent_real_le
import Theorems.Thm_TwoDegenerateGraphs_hammingParentTuple_card

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (hdimension : 0 < dimension)
    (side : Bool)
    (threshold : ℝ) :
    (hammingRetentionMeasure dimension).real
        (badPairLayerRetentionEvent parentCount dimension side threshold) ≤
      (((2 ^ (dimension * parentCount) : ℕ) : ℝ) *
        (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold)) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) := by
  classical
  let bound : ℝ :=
    ((((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
      Real.exp
        ((parentCount.choose 2 : ℝ) * Real.log 2 *
          (dimension : ℝ) * threshold)) *
        hammingRetentionProbability dimension ^
          (parentCount.choose 2)
  calc
    (hammingRetentionMeasure dimension).real
        (badPairLayerRetentionEvent parentCount dimension side threshold) =
      (hammingRetentionMeasure dimension).real
        (⋃ parents : Fin parentCount → HammingWord dimension,
          badPairChildRetentionEvent parents side threshold) := by
        rfl
    _ ≤ ∑ parents : Fin parentCount → HammingWord dimension,
          (hammingRetentionMeasure dimension).real
            (badPairChildRetentionEvent parents side threshold) :=
        MeasureTheory.measureReal_iUnion_fintype_le
          (fun parents => badPairChildRetentionEvent parents side threshold)
    _ ≤ ∑ _parents : Fin parentCount → HammingWord dimension, bound := by
      apply Finset.sum_le_sum
      intro parents _
      exact badPairChildRetentionEvent_real_le
        hparents hdimension parents side threshold
    _ =
      (((2 ^ (dimension * parentCount) : ℕ) : ℝ) *
        (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold)) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        hammingParentTuple_card]
      dsimp [bound]
      ring
end TwoDegenerateGraphs
