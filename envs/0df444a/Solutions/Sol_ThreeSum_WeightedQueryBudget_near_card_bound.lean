-- Prove2me | solution 1 for ThreeSum.WeightedQueryBudget.near_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:58:51.868869+00:00
-- url     : https://prove2.me/submissions/8ec9b525-cb0a-4fd2-876e-85e16067584d

import Definitions.Def_Submission_Weighted_PreparedWanted
import Definitions.Def_Submission_Weighted_Schedule
import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_Weighted_QueryBudget
import Theorems.Thm_ThreeSum_WeightedQueryBudget_z_pos
import Theorems.Thm_ThreeSum_WeightedQueryBudget_z_lt_one
import Theorems.Thm_ThreeSum_WeightedQueryBudget_gibbs_expression
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_codes_length_gibbs
import Theorems.Thm_ThreeSum_TernaryNearBankEnumeration_codes_length_eq_nearWords_card
import Theorems.Thm_ThreeSum_TernaryNearBankEnumeration_codes_length_gibbs
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_codes_length_gibbs
import Theorems.Thm_ThreeSum_WeightedFrozenQueryCost_polynomial_product_counts
import Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_codes_length_eq_nearWords_card
import Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_codes_length_gibbs


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedQueryBudget
open Real TernaryJointType WeightedSchedule WeightedCacheParameters
open WeightedBankEnumeration (cacheCost)
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
namespace ThreeSum.WeightedQueryBudget
theorem _root_.solution {m : ℕ} (Q : TritWord (fixedLength m))
    (hQ : HasType Q (fixedPi m)) :
    ((WeightedNearBankEnumeration.nearWords Q (treeBudget m)).card : ℝ)≤envelope m := by
  have hg := WeightedNearBankEnumeration.codes_length_gibbs Q (treeBudget m) zRoot z_pos.le z_lt_one.le
  rw [WeightedNearBankEnumeration.codes_length_eq_nearWords_card,
    WeightedFrozenQueryCost.polynomial_product_counts] at hg
  rw [←gibbs_expression Q hQ]
  exact (le_div_iff₀ (pow_pos z_pos _)).mpr hg
end ThreeSum.WeightedQueryBudget
