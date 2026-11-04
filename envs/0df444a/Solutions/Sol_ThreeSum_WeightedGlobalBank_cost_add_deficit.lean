-- Prove2me | solution 1 for ThreeSum.WeightedGlobalBank.cost_add_deficit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:19:18.488862+00:00
-- url     : https://prove2.me/submissions/4375e635-ee57-4479-b298-07b1ce7adc20

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_Weighted_FrozenQueryCost
import Definitions.Def_Submission_Weighted_GlobalBank
import Theorems.Thm_WeightedCache_concrete_cost_mono
import Theorems.Thm_WeightedCache_cost_add_deficit


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalBank
open TernaryJointType
namespace ThreeSum.WeightedGlobalBank
theorem _root_.solution {N : ℕ} {R Q : TritWord N} (h : Below R Q) :
    cacheCost R+deficit Q R=cacheCost Q :=
  WeightedCache.cost_add_deficit WeightedCache.concrete_cost_mono h
end ThreeSum.WeightedGlobalBank
