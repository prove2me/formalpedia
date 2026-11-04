-- Prove2me | solution 1 for ThreeSum.TernaryAddresses.mem_codes_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:27:09.943369+00:00
-- url     : https://prove2.me/submissions/2d340394-2af2-4608-97d2-a041d2143d68

import Definitions.Def_Submission_ThreeSum_TernaryEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Theorems.Thm_ThreeSum_TernaryAddresses_code_lt
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_eq_map
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_words
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits


attribute [local simp] ThreeSum.TernaryAddresses.codes_length

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryAddresses
open ThreeSum.TernaryEnumeration
namespace ThreeSum.TernaryAddresses
theorem _root_.solution {n t a : ℕ} (ha : a ∈ codes n t) : a < 4 ^ n := by
  rw [codes_eq_map] at ha
  obtain ⟨xs, hx, rfl⟩ := List.mem_map.mp ha
  obtain ⟨hlen, hall, _⟩ := (mem_words n t xs).mp hx
  simpa [hlen] using code_lt xs hall
end ThreeSum.TernaryAddresses
