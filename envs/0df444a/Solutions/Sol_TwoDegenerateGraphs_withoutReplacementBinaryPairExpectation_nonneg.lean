-- Prove2me | solution 1 for TwoDegenerateGraphs.withoutReplacementBinaryPairExpectation_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/2eb2ee2c-12f4-4f96-b455-0dd5974d0fb3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_withoutReplacementBinaryPairMass_nonneg

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (f : Bool → Bool → ℝ)
    (hf : ∀ left right, 0 ≤ f left right) :
    0 ≤ withoutReplacementBinaryPairExpectation parentCount oneCount f := by
  unfold withoutReplacementBinaryPairExpectation
  apply Finset.sum_nonneg
  intro left _
  apply Finset.sum_nonneg
  intro right _
  exact mul_nonneg
    (withoutReplacementBinaryPairMass_nonneg
      parentCount oneCount hparents hones left right)
    (hf left right)
end TwoDegenerateGraphs
