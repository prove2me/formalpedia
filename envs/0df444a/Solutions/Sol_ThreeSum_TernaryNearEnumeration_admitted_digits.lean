-- Prove2me | solution 1 for ThreeSum.TernaryNearEnumeration.admitted_digits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:37:48.154354+00:00
-- url     : https://prove2.me/submissions/dc096b79-caa8-402f-80bf-fd9ffe68b271

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
theorem _root_.solution {qs rs : List ℕ} {D : ℕ}
    (hq : ∀ q ∈ qs, q < 3) (h : Admitted qs rs D) : ∀ r ∈ rs, r < 3 := by
  induction qs generalizing rs D with
  | nil => cases rs <;> simp_all [Admitted]
  | cons q qs ih =>
    cases rs with
    | nil => simp [Admitted] at h
    | cons r rs =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h.1.trans_lt (hq q (by simp))
      · exact ih (fun y hy => hq y (by simp [hy])) h.2.2 x hx
end ThreeSum.TernaryNearEnumeration
