-- Prove2me | solution 1 for TwoDegenerateGraphs.empiricalChildMarginal_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/24d51b7c-497b-4e99-9764-d5818f011cd0

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_withoutReplacementBinaryPairExpectation_nonneg
import Theorems.Thm_TwoDegenerateGraphs_withoutReplacementBinaryPairExpectation_le_one

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (kernel : BinaryPairKernel) :
    0 ≤ empiricalChildMarginal parentCount oneCount kernel ∧
      empiricalChildMarginal parentCount oneCount kernel ≤ 1 := by
  constructor
  · exact withoutReplacementBinaryPairExpectation_nonneg
      parentCount oneCount hparents hones kernel.childProbability
      kernel.childProbability_nonneg
  · exact withoutReplacementBinaryPairExpectation_le_one
      parentCount oneCount hparents hones kernel.childProbability
      kernel.childProbability_le_one
end TwoDegenerateGraphs
