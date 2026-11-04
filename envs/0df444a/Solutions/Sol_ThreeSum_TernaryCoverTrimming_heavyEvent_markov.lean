-- Prove2me | solution 1 for ThreeSum.TernaryCoverTrimming.heavyEvent_markov
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:45:51.227144+00:00
-- url     : https://prove2.me/submissions/d91b905a-ac1a-453b-b085-b98fbc83bb70

import Definitions.Def_Submission_ThreeSum_TernaryCoverHashes
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverTrimming
open Finset TernaryCoverHashes
open scoped BigOperators
variable {ι K : Type*} [Fintype ι] [DecidableEq ι]
variable [Field K] [Fintype K] [DecidableEq K]
namespace ThreeSum.TernaryCoverTrimming
theorem _root_.solution (event : Finset (Weight (ι := ι) (K := K)))
    (vertices : Finset (Word (ι := ι) (K := K)))
    (vector : Word (ι := ι) (K := K) → Coordinate ι → K) (a : K) (B : ℕ) :
    B * (heavyEvent event vertices vector a B).card ≤
      loadedMass event vertices vector a := by
  calc
    _ = ∑ _w ∈ heavyEvent event vertices vector a B, B := by simp [Nat.mul_comm]
    _ ≤ ∑ w ∈ heavyEvent event vertices vector a B, bucketSize vertices vector w a :=
      sum_le_sum fun w hw => (mem_filter.mp hw).2.le
    _ ≤ loadedMass event vertices vector a :=
      sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => Nat.zero_le _)
end ThreeSum.TernaryCoverTrimming
