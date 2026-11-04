-- Prove2me | solution 1 for ThreeSum.WeightedGlobalBank.mem_nearWords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:19:15.262087+00:00
-- url     : https://prove2.me/submissions/56f4e06e-612f-4156-9eac-0bbb631b4a41

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_Weighted_FrozenQueryCost
import Definitions.Def_Submission_Weighted_GlobalBank
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.WeightedNearBankEnumeration.mem_nearWords



set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalBank
open TernaryJointType
namespace ThreeSum.WeightedGlobalBank
theorem _root_.solution {N D : ℕ} {R Q : TritWord N} :
    R∈nearWords Q D ↔ Below R Q ∧ deficit Q R≤D := WeightedNearBankEnumeration.mem_nearWords
end ThreeSum.WeightedGlobalBank
