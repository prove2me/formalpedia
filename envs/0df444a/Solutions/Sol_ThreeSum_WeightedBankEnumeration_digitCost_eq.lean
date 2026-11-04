-- Prove2me | solution 1 for ThreeSum.WeightedBankEnumeration.digitCost_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:37:16.495537+00:00
-- url     : https://prove2.me/submissions/1baf83be-783a-4e72-893b-ce320bc4100a

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_Weighted_BankEnumeration

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedBankEnumeration
open ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.TernaryJointType
namespace ThreeSum.WeightedBankEnumeration
theorem _root_.solution (d : Fin 3) : digitCost d.val = (![0,512,1025] : Fin 3→ℕ) d := by
  fin_cases d <;> norm_num [digitCost]
end ThreeSum.WeightedBankEnumeration
