-- Prove2me | solution 1 for ThreeSum.TernaryBankEnumeration.words_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:37:49.99521+00:00
-- url     : https://prove2.me/submissions/4eee3f2c-86be-469a-80fc-d963ad6b2dc9

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_eq_map
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_nodup


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.TernaryJointType ThreeSum.TernaryBank
namespace ThreeSum.TernaryBankEnumeration
theorem _root_.solution (N T : ℕ) : (words N T).Nodup := by
  have hc := codes_nodup N T
  rw [codes_eq_map] at hc
  exact List.Nodup.of_map code hc
end ThreeSum.TernaryBankEnumeration
