-- Prove2me | solution 1 for TwoDegenerateGraphs.pairTypeGroup_probability_mul_childComplement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/f8da862b-f0ab-4c28-85d0-531386be638e

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairTypeGroup_probability_mul_childRatio

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) :
    ((pairTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose 2 : ℝ) *
      (1 -
        ((pairTypeGroupChildOnes parents children
            coordinate bitType).card : ℝ) /
          ((pairTypeGroup parents coordinate bitType).card : ℝ)) =
      (((pairTypeGroup parents coordinate bitType).card : ℝ) -
        ((pairTypeGroupChildOnes parents children
          coordinate bitType).card : ℝ)) /
          (parentCount.choose 2 : ℝ) := by
  calc
    ((pairTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose 2 : ℝ) *
      (1 -
        ((pairTypeGroupChildOnes parents children
            coordinate bitType).card : ℝ) /
          ((pairTypeGroup parents coordinate bitType).card : ℝ)) =
      ((pairTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) -
        (((pairTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) *
            (((pairTypeGroupChildOnes parents children
              coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ))) := by
          ring
    _ = ((pairTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) -
        ((pairTypeGroupChildOnes parents children
          coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) := by
          rw [pairTypeGroup_probability_mul_childRatio
            hparents parents children coordinate bitType]
    _ = (((pairTypeGroup parents coordinate bitType).card : ℝ) -
        ((pairTypeGroupChildOnes parents children
          coordinate bitType).card : ℝ)) /
          (parentCount.choose 2 : ℝ) := by
          ring
end TwoDegenerateGraphs
