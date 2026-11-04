-- Prove2me | solution 1 for ThreeSum.TernaryNearEnumeration.admitted_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:37:44.764201+00:00
-- url     : https://prove2.me/submissions/3f7229f1-8be8-48ff-ba8a-0b7a41bc96eb

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits


attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearEnumeration
open ThreeSum.TernaryAddresses
namespace ThreeSum.TernaryNearEnumeration
theorem _root_.solution {qs rs : List ℕ} {D : ℕ} (h : Admitted qs rs D) :
    rs.length = qs.length := by
  induction qs generalizing rs D with
  | nil => cases rs <;> simp_all [Admitted]
  | cons q qs ih =>
    cases rs with
    | nil => simp [Admitted] at h
    | cons r rs => simpa only [List.length_cons] using congrArg Nat.succ (ih h.2.2)
end ThreeSum.TernaryNearEnumeration
