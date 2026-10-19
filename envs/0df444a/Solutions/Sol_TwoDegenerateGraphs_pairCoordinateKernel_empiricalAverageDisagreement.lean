-- Prove2me | solution 1 for TwoDegenerateGraphs.pairCoordinateKernel_empiricalAverageDisagreement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/a62ddf4e-e70d-4e20-b7cf-60d5a118b51f

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairCoordinateKernel_childProbability
import Theorems.Thm_TwoDegenerateGraphs_pairTypeGroup_probability_mul_childRatio
import Theorems.Thm_TwoDegenerateGraphs_withoutReplacementBinaryPairMass_eq_pairTypeGroup
import Theorems.Thm_TwoDegenerateGraphs_pairTypeGroup_probability_mul_childComplement

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
    empiricalAverageDisagreement parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      (((pairTypeGroupChildOnes parents children coordinate 0).card : ℝ) +
        ((pairTypeGroup parents coordinate 2).card : ℝ) / 2 +
        (((pairTypeGroup parents coordinate 1).card : ℝ) -
          ((pairTypeGroupChildOnes parents children coordinate 1).card : ℝ))) /
        (parentCount.choose 2 : ℝ) := by
  have hzero := pairTypeGroup_probability_mul_childRatio
    hparents parents children coordinate 0
  have hone := pairTypeGroup_probability_mul_childComplement
    hparents parents children coordinate 1
  calc
    empiricalAverageDisagreement parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      ((pairTypeGroup parents coordinate 0).card : ℝ) /
          (parentCount.choose 2 : ℝ) *
        (((pairTypeGroupChildOnes parents children
          coordinate 0).card : ℝ) /
            ((pairTypeGroup parents coordinate 0).card : ℝ)) +
      ((pairTypeGroup parents coordinate 2).card : ℝ) /
          (parentCount.choose 2 : ℝ) * (1 / 2 : ℝ) +
      ((pairTypeGroup parents coordinate 1).card : ℝ) /
          (parentCount.choose 2 : ℝ) *
        (1 -
          ((pairTypeGroupChildOnes parents children
            coordinate 1).card : ℝ) /
              ((pairTypeGroup parents coordinate 1).card : ℝ)) := by
      unfold empiricalAverageDisagreement
        withoutReplacementBinaryPairExpectation
      simp_rw [withoutReplacementBinaryPairMass_eq_pairTypeGroup
        hparents parents coordinate]
      simp [Fintype.univ_bool,
        pairCoordinateKernel_childProbability,
        pairBitTypeOfOutcomes,
        BinaryPairKernel.bitDisagreementProbability]
      ring
    _ =
      (((pairTypeGroupChildOnes parents children coordinate 0).card : ℝ) +
        ((pairTypeGroup parents coordinate 2).card : ℝ) / 2 +
        (((pairTypeGroup parents coordinate 1).card : ℝ) -
          ((pairTypeGroupChildOnes parents children coordinate 1).card : ℝ))) /
        (parentCount.choose 2 : ℝ) := by
      rw [hzero, hone]
      ring
end TwoDegenerateGraphs
