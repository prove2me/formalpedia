-- Prove2me | solution 1 for P2M_ThreeSum_TernaryNearEnumeration_admitted_forall__67eef609a191
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:37:45.719177+00:00
-- url     : https://prove2.me/submissions/2b9b13e8-2d74-4fc0-b656-325cc7e86ffc

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
    List.Forall₂ (· ≤ ·) rs qs := by
  induction qs generalizing rs D with
  | nil => cases rs <;> simp_all [Admitted]
  | cons q qs ih =>
    cases rs with
    | nil => simp [Admitted] at h
    | cons r rs => exact List.Forall₂.cons h.1 (ih h.2.2)
end ThreeSum.TernaryNearEnumeration
