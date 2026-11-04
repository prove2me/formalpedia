-- Prove2me | solution 1 for ThreeSum.WeightedGlobalBank.mem_bank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:16:07.981738+00:00
-- url     : https://prove2.me/submissions/fc44b120-ee35-4bed-8211-e892078452b6

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_Weighted_FrozenQueryCost
import Definitions.Def_Submission_Weighted_GlobalBank
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.WeightedBankEnumeration.mem_bank



set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalBank
open TernaryJointType
namespace ThreeSum.WeightedGlobalBank
theorem _root_.solution {N T : ℕ} {R : TritWord N} : R∈bank N T ↔ cacheCost R≤T :=
  WeightedBankEnumeration.mem_bank
end ThreeSum.WeightedGlobalBank
