-- Prove2me | solution 1 for TwoDegenerateGraphs.empiricalConditionalEntropy_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/8550b991-2f40-49cc-b2ee-a2c5aec05d31

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_binaryEntropy_nonneg
import Theorems.Thm_TwoDegenerateGraphs_binaryEntropy_le_one
import Theorems.Thm_TwoDegenerateGraphs_withoutReplacementBinaryPairExpectation_error

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (kernel : BinaryPairKernel)
    (hparameter :
      kernel.parentProbability =
        (oneCount : ℝ) / (parentCount : ℝ)) :
    |empiricalConditionalEntropy parentCount oneCount kernel -
      kernel.conditionalEntropy| ≤ 1 / (parentCount : ℝ) := by
  have herror := withoutReplacementBinaryPairExpectation_error
    parentCount oneCount hparents hones
    (fun left right => binaryEntropy (kernel.childProbability left right))
    (fun left right =>
      ⟨binaryEntropy_nonneg
        (kernel.childProbability_nonneg left right)
        (kernel.childProbability_le_one left right),
        binaryEntropy_le_one (kernel.childProbability left right)⟩)
  rw [← hparameter] at herror
  simpa [empiricalConditionalEntropy,
    BinaryPairKernel.conditionalEntropy] using herror
end TwoDegenerateGraphs
