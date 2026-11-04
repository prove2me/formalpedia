-- Prove2me | solution 1 for ThreeSum.TernaryNearEnumeration.visits_le_codes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:08:27.53089+00:00
-- url     : https://prove2.me/submissions/f8b14838-356a-49b3-bdb3-c90d5d4ba4be

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_visits_le
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryEnumeration_visits_le
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits


attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryNearEnumeration.codes_length

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearEnumeration
open ThreeSum.TernaryAddresses
namespace ThreeSum.TernaryNearEnumeration
theorem _root_.solution (qs : List ℕ) (D : ℕ) :
    visits qs D ≤ (qs.length+1)*(codes qs D).length := by
  simpa only [codes_length] using visits_le qs D
end ThreeSum.TernaryNearEnumeration
