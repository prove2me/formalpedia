-- Prove2me | solution 1 for ThreeSum.TernaryAddresses.codes_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:26:34.338786+00:00
-- url     : https://prove2.me/submissions/c37ebd55-30ca-4be3-89f6-a81982629975

import Definitions.Def_Submission_ThreeSum_TernaryEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_eq_map
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryAddresses
open ThreeSum.TernaryEnumeration
namespace ThreeSum.TernaryAddresses
theorem _root_.solution (n t : ℕ) : (codes n t).length = (words n t).length := by
  simp [codes_eq_map]
end ThreeSum.TernaryAddresses
