-- Prove2me | solution 1 for TwoDegenerateGraphs.withoutReplacementBinaryPairExpectation_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/e72d2050-e88e-4e7a-8ab1-6d02a2acc685

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_withoutReplacementBinaryPairMass_nonneg
import Theorems.Thm_TwoDegenerateGraphs_withoutReplacementBinaryPairMass_sum

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (f : Bool → Bool → ℝ)
    (hf : ∀ left right, f left right ≤ 1) :
    withoutReplacementBinaryPairExpectation parentCount oneCount f ≤ 1 := by
  unfold withoutReplacementBinaryPairExpectation
  calc
    (∑ left : Bool, ∑ right : Bool,
        withoutReplacementBinaryPairMass parentCount oneCount left right *
          f left right) ≤
      ∑ left : Bool, ∑ right : Bool,
        withoutReplacementBinaryPairMass parentCount oneCount left right * 1 := by
          apply Finset.sum_le_sum
          intro left _
          apply Finset.sum_le_sum
          intro right _
          exact mul_le_mul_of_nonneg_left (hf left right)
            (withoutReplacementBinaryPairMass_nonneg
              parentCount oneCount hparents hones left right)
    _ = 1 := by
      simpa using
        withoutReplacementBinaryPairMass_sum parentCount oneCount hparents
end TwoDegenerateGraphs
