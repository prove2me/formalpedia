-- Prove2me | solution 1 for TwoDegenerateGraphs.pairCoordinateConditionalEntropy_log_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/ab10400e-3565-4d69-a82f-69d75b36603e

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairCoordinateConditionalEntropy_mass

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    {parentCount dimension : ℕ} (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ bitType : PairBitType,
      ((pairTypeGroup parents coordinate bitType).card : ℝ) *
        Real.binEntropy
          (((pairTypeGroupChildOnes parents children
              coordinate bitType).card : ℝ) /
            ((pairTypeGroup parents coordinate bitType).card : ℝ))) =
      (parentCount.choose 2 : ℝ) * Real.log 2 *
        pairCoordinateConditionalEntropy parents children coordinate := by
  calc
    (∑ bitType : PairBitType,
        ((pairTypeGroup parents coordinate bitType).card : ℝ) *
          Real.binEntropy
            (((pairTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ))) =
      (∑ bitType : PairBitType,
        ((pairTypeGroup parents coordinate bitType).card : ℝ) *
          binaryEntropy
            (((pairTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ))) *
        Real.log 2 := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro bitType _
          unfold binaryEntropy
          field_simp [log_two_pos.ne']
    _ = (parentCount.choose 2 : ℝ) * Real.log 2 *
        pairCoordinateConditionalEntropy parents children coordinate := by
      rw [← pairCoordinateConditionalEntropy_mass
        hparents parents children coordinate]
      ring
end TwoDegenerateGraphs
