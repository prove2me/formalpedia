-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedQueryBudget.near_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:14:01.126603+00:00
-- url     : https://prove2.me/submissions/c6608b29-c05f-4bb5-b6bf-1d8e24c298c4

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PreparedWanted
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Schedule
import Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_QueryBudget
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedQueryBudget_z_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedQueryBudget_z_lt_one
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedQueryBudget_gibbs_expression
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_codes_length_gibbs
import Theorems.Thm_ThreeSum_TernaryNearBankEnumeration_codes_length_eq_nearWords_card
import Theorems.Thm_ThreeSum_TernaryNearBankEnumeration_codes_length_gibbs
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_codes_length_gibbs
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrozenQueryCost_polynomial_product_counts
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearBankEnumeration_codes_length_eq_nearWords_card
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearBankEnumeration_codes_length_gibbs


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedQueryBudget
open Real TernaryJointType WeightedSchedule WeightedCacheParameters_e1ae71d
open WeightedBankEnumeration (cacheCost)
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedQueryBudget
theorem _root_.solution {m : ℕ} (Q : TritWord (fixedLength m))
    (hQ : HasType Q (fixedPi m)) :
    ((WeightedNearBankEnumeration.nearWords Q (treeBudget m)).card : ℝ)≤envelope m := by
  have hg := WeightedNearBankEnumeration.codes_length_gibbs Q (treeBudget m) zRoot z_pos.le z_lt_one.le
  rw [WeightedNearBankEnumeration.codes_length_eq_nearWords_card,
    WeightedFrozenQueryCost.polynomial_product_counts] at hg
  rw [←gibbs_expression Q hQ]
  exact (le_div_iff₀ (pow_pos z_pos _)).mpr hg
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedQueryBudget
