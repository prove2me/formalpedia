-- Prove2me | solution 1 for TwoDegenerateGraphs.BinaryPairKernel.childMarginal_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/f820ef8a-8ee4-4efa-8493-18dc0e992181

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_independentBinaryPairMass_nonneg
import Theorems.Thm_TwoDegenerateGraphs_independentBinaryPairMass_sum

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
open TwoDegenerateGraphs.BinaryPairKernel
namespace TwoDegenerateGraphs.BinaryPairKernel
theorem _root_.solution (kernel : BinaryPairKernel) :
    kernel.childMarginal ≤ 1 := by
  unfold childMarginal
  calc
    (∑ left : Bool, ∑ right : Bool,
        independentBinaryPairMass kernel.parentProbability left right *
          kernel.childProbability left right) ≤
      ∑ left : Bool, ∑ right : Bool,
        independentBinaryPairMass kernel.parentProbability left right * 1 := by
          apply Finset.sum_le_sum
          intro left _
          apply Finset.sum_le_sum
          intro right _
          exact mul_le_mul_of_nonneg_left
            (kernel.childProbability_le_one left right)
            (independentBinaryPairMass_nonneg
              kernel.parentProbability_nonneg kernel.parentProbability_le_one
              left right)
    _ = 1 := by
      simpa using independentBinaryPairMass_sum kernel.parentProbability
end TwoDegenerateGraphs.BinaryPairKernel
