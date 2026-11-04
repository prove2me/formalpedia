-- Prove2me | solution 1 for ThreeSum.TernaryCoverTrimming.heavyEvent_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:46:39.037272+00:00
-- url     : https://prove2.me/submissions/a89022e6-e34b-48c4-9cff-4498a18b60c8

import Definitions.Def_Submission_ThreeSum_TernaryCoverHashes
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming
import Theorems.Thm_ThreeSum_TernaryCoverTrimming_heavyEvent_markov
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverTrimming
open Finset TernaryCoverHashes
open scoped BigOperators
variable {ι K : Type*} [Fintype ι] [DecidableEq ι]
variable [Field K] [Fintype K] [DecidableEq K]
namespace ThreeSum.TernaryCoverTrimming
theorem _root_.solution (x y : Word (ι := ι) (K := K)) (a b target : K)
    (vertices : Finset (Word (ι := ι) (K := K)))
    (vector : Word (ι := ι) (K := K) → Coordinate ι → K) (B : ℕ)
    (hload : Fintype.card K ^ 3 * loadedMass (pairEvent x y a b) vertices vector target ≤
      (Fintype.card K + vertices.card) * Fintype.card (Weight (ι := ι) (K := K)))
    (hB : 8 * (Fintype.card K + vertices.card) ≤ B * Fintype.card K) :
    8 * Fintype.card K ^ 2 * (heavyEvent (pairEvent x y a b) vertices vector target B).card ≤
      Fintype.card (Weight (ι := ι) (K := K)) := by
  have hm := heavyEvent_markov (pairEvent x y a b) vertices vector target B
  have hp : 0 < Fintype.card K := Fintype.card_pos
  have hpos : 0 < B * Fintype.card K := lt_of_lt_of_le (by omega) hB
  apply Nat.le_of_mul_le_mul_left (c := B * Fintype.card K) ?_ hpos
  calc
    _ = 8 * (Fintype.card K ^ 3 *
        (B * (heavyEvent (pairEvent x y a b) vertices vector target B).card)) := by ring
    _ ≤ 8 * (Fintype.card K ^ 3 * loadedMass (pairEvent x y a b) vertices vector target) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hm)
    _ ≤ 8 * ((Fintype.card K + vertices.card) * Fintype.card (Weight (ι := ι) (K := K))) :=
      Nat.mul_le_mul_left _ hload
    _ ≤ _ := by
      simpa only [Nat.mul_assoc] using
        Nat.mul_le_mul_right (Fintype.card (Weight (ι := ι) (K := K))) hB
end ThreeSum.TernaryCoverTrimming
