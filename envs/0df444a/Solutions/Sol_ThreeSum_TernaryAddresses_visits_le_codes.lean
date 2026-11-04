-- Prove2me | solution 1 for ThreeSum.TernaryAddresses.visits_le_codes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:28:26.938511+00:00
-- url     : https://prove2.me/submissions/032d8760-3d3e-40e3-96ee-6b118a903990

import Definitions.Def_Submission_ThreeSum_TernaryEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryEnumeration_visits_le
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits


attribute [local simp] ThreeSum.TernaryAddresses.codes_length

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryAddresses
open ThreeSum.TernaryEnumeration
namespace ThreeSum.TernaryAddresses
theorem _root_.solution (n t : ℕ) : visits n t ≤ (n + 1) * (codes n t).length := by
  simpa only [codes_length] using visits_le n t
end ThreeSum.TernaryAddresses
