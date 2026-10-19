-- Prove2me | solution 1 for TwoDegenerateGraphs.empiricalChildMarginal_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/aeb5af3e-fae9-4b8f-a2ce-1298b9ced254

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
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
    |empiricalChildMarginal parentCount oneCount kernel -
      kernel.childMarginal| ≤ 1 / (parentCount : ℝ) := by
  have herror := withoutReplacementBinaryPairExpectation_error
    parentCount oneCount hparents hones
    kernel.childProbability
    (fun left right =>
      ⟨kernel.childProbability_nonneg left right,
        kernel.childProbability_le_one left right⟩)
  rw [← hparameter] at herror
  simpa [empiricalChildMarginal, BinaryPairKernel.childMarginal] using herror
end TwoDegenerateGraphs
