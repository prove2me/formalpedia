-- Prove2me | solution 1 for ThreeSum.TernaryNearEnumeration.admitted_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:01:45.844203+00:00
-- url     : https://prove2.me/submissions/26179c02-c22c-4d9f-9dc6-12a64a3f53d7

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
import Theorems.Thm_P2M_ThreeSum_TernaryNearEnumeration_admitted_forall__67eef609a191
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_admitted_deficit
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits


attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearEnumeration
open ThreeSum.TernaryAddresses
namespace ThreeSum.TernaryNearEnumeration
theorem _root_.solution (qs rs : List ℕ) (D : ℕ) :
    Admitted qs rs D ↔ List.Forall₂ (· ≤ ·) rs qs ∧
      (List.zipWith Nat.sub qs rs).sum ≤ D := by
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
end ThreeSum.TernaryNearEnumeration
