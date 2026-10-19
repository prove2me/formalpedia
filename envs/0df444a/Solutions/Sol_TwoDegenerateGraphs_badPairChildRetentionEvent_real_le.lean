-- Prove2me | solution 1 for TwoDegenerateGraphs.badPairChildRetentionEvent_real_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/289f11ba-c5c3-452b-be93-f5ab90621009

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_badPairChildArrays_card_le
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_real_pairChildren

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (hdimension : 0 < dimension)
    (parents : Fin parentCount → HammingWord dimension)
    (side : Bool)
    (threshold : ℝ) :
    (hammingRetentionMeasure dimension).real
        (badPairChildRetentionEvent parents side threshold) ≤
      ((((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold)) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) := by
  classical
  let distinctBad :
      Finset (PairLayer parentCount 1 → HammingWord dimension) :=
    (badPairChildArrays parents threshold).filter Function.Injective
  have hprobability_nonneg :
      0 ≤ hammingRetentionProbability dimension ^
        (parentCount.choose 2) :=
    pow_nonneg (hammingRetentionProbability_pos dimension).le _
  have hcard :
      (distinctBad.card : ℝ) ≤
        ((badPairChildArrays parents threshold).card : ℝ) := by
    dsimp [distinctBad]
    exact_mod_cast
      Finset.card_filter_le
        (badPairChildArrays parents threshold) Function.Injective
  calc
    (hammingRetentionMeasure dimension).real
        (badPairChildRetentionEvent parents side threshold) =
      (hammingRetentionMeasure dimension).real
        (⋃ children ∈ distinctBad,
          pairChildRetentionEvent side children) := by
        rfl
    _ ≤ ∑ children ∈ distinctBad,
          (hammingRetentionMeasure dimension).real
            (pairChildRetentionEvent side children) :=
        MeasureTheory.measureReal_biUnion_finset_le
          distinctBad (pairChildRetentionEvent side)
    _ = ∑ _children ∈ distinctBad,
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) := by
        apply Finset.sum_congr rfl
        intro children hchildren
        have hinjective : Function.Injective children := by
          have hmembership :
              children ∈
                (badPairChildArrays parents threshold).filter
                  Function.Injective := by
            simpa only [distinctBad] using hchildren
          exact (Finset.mem_filter.mp hmembership).2
        exact hammingRetentionMeasure_real_pairChildren
          side children hinjective
    _ = (distinctBad.card : ℝ) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) := by
        simp [nsmul_eq_mul]
    _ ≤ ((badPairChildArrays parents threshold).card : ℝ) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) :=
        mul_le_mul_of_nonneg_right hcard hprobability_nonneg
    _ ≤
      ((((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold)) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) :=
        mul_le_mul_of_nonneg_right
          (badPairChildArrays_card_le hparents hdimension parents threshold)
          hprobability_nonneg
end TwoDegenerateGraphs
