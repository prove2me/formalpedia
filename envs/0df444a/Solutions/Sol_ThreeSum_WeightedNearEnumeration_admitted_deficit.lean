-- Prove2me | solution 1 for ThreeSum.WeightedNearEnumeration.admitted_deficit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:37:22.96803+00:00
-- url     : https://prove2.me/submissions/943b2170-237a-4c9d-a054-8a9e2654fa9c

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_NearEnumeration
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.WeightedAddresses.codes_length
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] ThreeSum.WeightedEnumeration.mem_digits


attribute [local simp] ThreeSum.WeightedNearEnumeration.mem_digits

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearEnumeration
open ThreeSum.WeightedAddresses ThreeSum.WeightedEnumeration
namespace ThreeSum.WeightedNearEnumeration
theorem _root_.solution {qs rs : List ℕ} {D : ℕ} (h : Admitted qs rs D) :
    (List.zipWith (fun q r => digitCost q-digitCost r) qs rs).sum ≤ D := by
  induction qs generalizing rs D with
  | nil => cases rs <;> simp_all [Admitted]
  | cons q qs ih =>
    cases rs with
    | nil => simp [Admitted] at h
    | cons r rs =>
      have ht := ih h.2.2
      simp only [List.zipWith_cons_cons,List.sum_cons]
      change digitCost q-digitCost r+(List.zipWith (fun q r => digitCost q-digitCost r) qs rs).sum ≤ D
      have hd := h.2.1
      omega
end ThreeSum.WeightedNearEnumeration
