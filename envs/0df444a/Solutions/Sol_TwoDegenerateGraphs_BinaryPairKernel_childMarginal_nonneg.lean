-- Prove2me | solution 1 for TwoDegenerateGraphs.BinaryPairKernel.childMarginal_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/5e106e8a-2954-465e-99a1-d61d9afdf5e3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_independentBinaryPairMass_nonneg

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
open TwoDegenerateGraphs.BinaryPairKernel
namespace TwoDegenerateGraphs.BinaryPairKernel
theorem _root_.solution (kernel : BinaryPairKernel) :
    0 ≤ kernel.childMarginal := by
  unfold childMarginal
  apply Finset.sum_nonneg
  intro left _
  apply Finset.sum_nonneg
  intro right _
  exact mul_nonneg
    (independentBinaryPairMass_nonneg
      kernel.parentProbability_nonneg kernel.parentProbability_le_one
      left right)
    (kernel.childProbability_nonneg left right)
end TwoDegenerateGraphs.BinaryPairKernel
