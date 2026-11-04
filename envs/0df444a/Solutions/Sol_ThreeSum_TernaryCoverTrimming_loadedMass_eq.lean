-- Prove2me | solution 1 for ThreeSum.TernaryCoverTrimming.loadedMass_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:45:34.159056+00:00
-- url     : https://prove2.me/submissions/f416a1c6-c11f-4c85-8d89-8ce332a64b57

import Definitions.Def_Submission_ThreeSum_TernaryCoverHashes
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverTrimming
open Finset TernaryCoverHashes
open scoped BigOperators
variable {ι K : Type*} [Fintype ι] [DecidableEq ι]
variable [Field K] [Fintype K] [DecidableEq K]
namespace ThreeSum.TernaryCoverTrimming
theorem _root_.solution (event : Finset (Weight (ι := ι) (K := K)))
    (vertices : Finset (Word (ι := ι) (K := K)))
    (vector : Word (ι := ι) (K := K) → Coordinate ι → K) (a : K) :
    loadedMass event vertices vector a =
      ∑ u ∈ vertices, (event.filter fun w => linearHash (vector u) w = a).card := by
  classical
  unfold loadedMass bucketSize
  simp_rw [card_eq_sum_ones, sum_filter]
  rw [sum_comm]
end ThreeSum.TernaryCoverTrimming
