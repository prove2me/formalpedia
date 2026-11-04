-- Prove2me | solution 1 for ThreeSum.LightWeightedCost.partialCost_address
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:38:48.580994+00:00
-- url     : https://prove2.me/submissions/f70f44fd-ee4d-4d8d-8ab7-c373c5883b8a

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_Weighted_LightCost
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_digit_eq
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_digitCost_eq


set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedCost
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
open ThreeSum.WeightedEnumeration
open Light Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.LightSubsetAddress
namespace ThreeSum.LightWeightedCost
theorem _root_.solution {N : ℕ} (w : TritWord N) : partialCost N (address w) N=WeightedBankEnumeration.cacheCost w := by
  unfold partialCost WeightedBankEnumeration.cacheCost WeightedCache.cost
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro i hi
  rw [show digitAt N (address w) i.val=(w i).val from digit_eq w i]
  exact WeightedBankEnumeration.digitCost_eq (w i)
end ThreeSum.LightWeightedCost
