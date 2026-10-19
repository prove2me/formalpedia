-- Prove2me | solution 1 for TwoDegenerateGraphs.pairCoordinateKernel_empiricalChildMarginal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/98f8f762-837e-4ded-894d-76ca3761bbf1

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairCoordinateKernel_childProbability
import Theorems.Thm_TwoDegenerateGraphs_sum_pairTypeGroupChildOnes_card
import Theorems.Thm_TwoDegenerateGraphs_pairTypeGroup_probability_mul_childRatio
import Theorems.Thm_TwoDegenerateGraphs_withoutReplacementBinaryPairMass_eq_pairTypeGroup

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
    (coordinate : Fin dimension) :
    empiricalChildMarginal parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      (pairChildCoordinateOneCount children coordinate : ℝ) /
        (parentCount.choose 2 : ℝ) := by
  have hgroups :
      (∑ bitType : PairBitType,
        ((pairTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) *
            (((pairTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ))) =
        (pairChildCoordinateOneCount children coordinate : ℝ) /
          (parentCount.choose 2 : ℝ) := by
    calc
      (∑ bitType : PairBitType,
        ((pairTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) *
            (((pairTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ))) =
        ∑ bitType : PairBitType,
          ((pairTypeGroupChildOnes parents children
            coordinate bitType).card : ℝ) /
              (parentCount.choose 2 : ℝ) := by
          apply Finset.sum_congr rfl
          intro bitType _
          exact pairTypeGroup_probability_mul_childRatio
            hparents parents children coordinate bitType
      _ =
        (∑ bitType : PairBitType,
          ((pairTypeGroupChildOnes parents children
            coordinate bitType).card : ℝ)) /
            (parentCount.choose 2 : ℝ) := by
          rw [Finset.sum_div]
      _ = (pairChildCoordinateOneCount children coordinate : ℝ) /
          (parentCount.choose 2 : ℝ) := by
          congr 1
          exact_mod_cast
            sum_pairTypeGroupChildOnes_card parents children coordinate
  calc
    empiricalChildMarginal parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      ∑ bitType : PairBitType,
        ((pairTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) *
            (((pairTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ)) := by
      unfold empiricalChildMarginal
        withoutReplacementBinaryPairExpectation
      simp_rw [withoutReplacementBinaryPairMass_eq_pairTypeGroup
        hparents parents coordinate]
      simp [Fintype.univ_bool,
        pairCoordinateKernel_childProbability,
        pairBitTypeOfOutcomes,
        Fin.sum_univ_succ]
      ring
    _ = (pairChildCoordinateOneCount children coordinate : ℝ) /
      (parentCount.choose 2 : ℝ) := hgroups
end TwoDegenerateGraphs
