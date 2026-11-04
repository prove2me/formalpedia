-- Prove2me | solution 1 for ThreeSum.TernaryNearEnumeration.admitted_deficit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:37:47.0322+00:00
-- url     : https://prove2.me/submissions/07c1f77d-c43c-47aa-8a56-5241e0b46e9e

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
    (List.zipWith Nat.sub qs rs).sum ≤ D := by
  induction qs generalizing rs D with
  | nil => cases rs <;> simp_all [Admitted]
  | cons q qs ih =>
    cases rs with
    | nil => simp [Admitted] at h
    | cons r rs =>
      have ht := ih h.2.2
      simp only [List.zipWith_cons_cons,List.sum_cons]
      change q-r+(List.zipWith Nat.sub qs rs).sum ≤ D
      have hd := h.2.1
      omega
end ThreeSum.TernaryNearEnumeration
