-- Prove2me | solution 1 for ThreeSum.WeightedBankEnumeration.words_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:37:18.304586+00:00
-- url     : https://prove2.me/submissions/a41c2a36-842b-433a-aa91-096a3d64cd8e

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_Weighted_BankEnumeration
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_eq_map
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_nodup
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_eq_map
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_nodup


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedBankEnumeration
open ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.TernaryJointType
namespace ThreeSum.WeightedBankEnumeration
theorem _root_.solution (N T : ℕ) : (words N T).Nodup := by
  have hc := codes_nodup N T
  rw [codes_eq_map] at hc
  exact List.Nodup.of_map code hc
end ThreeSum.WeightedBankEnumeration
