-- Prove2me | solution 1 for ThreeSum.TernaryCoverTrimming.trimmedPairEvent_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:30:43.771195+00:00
-- url     : https://prove2.me/submissions/9e03dab8-5fa6-43db-9c6a-89240dce6905

import Definitions.Def_Submission_ThreeSum_TernaryCoverHashes
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming
import Theorems.Thm_ThreeSum_TernaryCoverTrimming_left_loadedMass_bound
import Theorems.Thm_ThreeSum_TernaryCoverTrimming_right_loadedMass_bound
import Theorems.Thm_ThreeSum_TernaryCoverTrimming_heavyEvent_bound
import Theorems.Thm_ThreeSum_HashFamily_pairEvent_card
import Theorems.Thm_ThreeSum_TernaryCoverHashes_pairEvent_card


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverTrimming
open Finset TernaryCoverHashes
open scoped BigOperators
variable {ι K : Type*} [Fintype ι] [DecidableEq ι]
variable [Field K] [Fintype K] [DecidableEq K]
namespace ThreeSum.TernaryCoverTrimming
theorem _root_.solution (x y : Word (ι := ι) (K := K)) (a b : K)
    (VL VR : Finset (Word (ι := ι) (K := K))) (B : ℕ)
    (hBL : 8 * (Fintype.card K + VL.card) ≤ B * Fintype.card K)
    (hBR : 8 * (Fintype.card K + VR.card) ≤ B * Fintype.card K) :
    3 * Fintype.card (Weight (ι := ι) (K := K)) ≤
      4 * Fintype.card K ^ 2 * (trimmedPairEvent x y a b VL VR B).card := by
  classical
  have hsub : pairEvent x y a b ⊆
      (trimmedPairEvent x y a b VL VR B ∪
        heavyEvent (pairEvent x y a b) VL leftVector a B) ∪
          heavyEvent (pairEvent x y a b) VR rightVector b B := by
    intro w hw
    by_cases hl : bucketSize VL leftVector w a ≤ B
    · by_cases hr : bucketSize VR rightVector w b ≤ B
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hw, hl, hr⟩))
      · exact mem_union_right _ (mem_filter.mpr ⟨hw, by omega⟩)
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hw, by omega⟩))
  have hcard : (pairEvent x y a b).card ≤
      (trimmedPairEvent x y a b VL VR B).card +
        (heavyEvent (pairEvent x y a b) VL leftVector a B).card +
          (heavyEvent (pairEvent x y a b) VR rightVector b B).card :=
    (card_le_card hsub).trans ((card_union_le ..).trans (Nat.add_le_add_right (card_union_le ..) _))
  have hraw := pairEvent_card x y a b
  have hleft := heavyEvent_bound x y a b a VL leftVector B (left_loadedMass_bound x y a b VL) hBL
  have hright := heavyEvent_bound x y a b b VR rightVector B (right_loadedMass_bound x y a b VR) hBR
  have hscaled := Nat.mul_le_mul_left (8 * Fintype.card K ^ 2) hcard
  nlinarith
end ThreeSum.TernaryCoverTrimming
