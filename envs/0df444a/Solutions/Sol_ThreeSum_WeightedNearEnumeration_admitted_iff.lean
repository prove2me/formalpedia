-- Prove2me | solution 1 for ThreeSum.WeightedNearEnumeration.admitted_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:01:34.950183+00:00
-- url     : https://prove2.me/submissions/f5b5d165-6951-4871-bd33-371d420ab2d8

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_NearEnumeration
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_mem_digits
import Theorems.Thm_P2M_ThreeSum_WeightedNearEnumeration_admitted_forall__05cd4af26192
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_admitted_deficit
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
theorem _root_.solution (qs rs : List ℕ) (D : ℕ) :
    Admitted qs rs D ↔ List.Forall₂ (· ≤ ·) rs qs ∧
      (List.zipWith (fun q r => digitCost q-digitCost r) qs rs).sum ≤ D := by
  constructor
  · intro h
    exact ⟨admitted_forall₂ h,admitted_deficit h⟩
  · induction qs generalizing rs D with
    | nil =>
      cases rs <;> simp [Admitted]
    | cons q qs ih =>
      cases rs with
      | nil => simp [List.forall₂_cons]
      | cons r rs =>
        rintro ⟨hpair,hsum⟩
        have hp := List.forall₂_cons.mp hpair
        simp only [List.zipWith_cons_cons,List.sum_cons,Nat.sub_eq] at hsum
        refine ⟨hp.1,by omega,?_⟩
        apply ih
        exact ⟨hp.2,by omega⟩
end ThreeSum.WeightedNearEnumeration
