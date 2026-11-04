-- Prove2me | solution 1 for ThreeSum.TernaryNearEnumeration.mem_codes_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:06:22.607528+00:00
-- url     : https://prove2.me/submissions/63071d2f-5156-4b02-87ea-067d0e6ad3e2

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_words
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_admitted_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_admitted_digits
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_eq_map
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryAddresses_code_lt
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_eq_map
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_words
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits


attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryNearEnumeration.codes_length

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearEnumeration
open ThreeSum.TernaryAddresses
namespace ThreeSum.TernaryNearEnumeration
theorem _root_.solution {qs : List ℕ} {D a : ℕ}
    (hq : ∀ q ∈ qs, q < 3) (ha : a ∈ codes qs D) : a < 4^qs.length := by
  rw [codes_eq_map] at ha
  obtain ⟨rs,hrs,rfl⟩ := List.mem_map.mp ha
  have had := (mem_words qs rs D).mp hrs
  simpa only [admitted_length had] using code_lt rs (admitted_digits hq had)
end ThreeSum.TernaryNearEnumeration
