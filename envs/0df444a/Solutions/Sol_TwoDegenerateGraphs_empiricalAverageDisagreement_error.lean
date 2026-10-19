-- Prove2me | solution 1 for TwoDegenerateGraphs.empiricalAverageDisagreement_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/3d266c36-2620-47d5-9438-52aa7c8a1358

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_BinaryPairKernel_bitDisagreementProbability_mem_Icc
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
    |empiricalAverageDisagreement parentCount oneCount kernel -
      kernel.averageDisagreement| ≤ 1 / (parentCount : ℝ) := by
  let observable : Bool → Bool → ℝ := fun left right =>
    (BinaryPairKernel.bitDisagreementProbability left
        (kernel.childProbability left right) +
      BinaryPairKernel.bitDisagreementProbability right
        (kernel.childProbability left right)) / 2
  have hobservable (left right : Bool) :
      0 ≤ observable left right ∧ observable left right ≤ 1 := by
    have hleft := BinaryPairKernel.bitDisagreementProbability_mem_Icc left
      (kernel.childProbability left right)
      (kernel.childProbability_nonneg left right)
      (kernel.childProbability_le_one left right)
    have hright := BinaryPairKernel.bitDisagreementProbability_mem_Icc right
      (kernel.childProbability left right)
      (kernel.childProbability_nonneg left right)
      (kernel.childProbability_le_one left right)
    dsimp [observable]
    constructor <;> linarith
  have herror := withoutReplacementBinaryPairExpectation_error
    parentCount oneCount hparents hones observable hobservable
  rw [← hparameter] at herror
  simpa [empiricalAverageDisagreement,
    BinaryPairKernel.averageDisagreement, observable] using herror
end TwoDegenerateGraphs
