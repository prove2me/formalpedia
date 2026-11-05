-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedQueryBudget.bank_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:05:40.384884+00:00
-- url     : https://prove2.me/submissions/dcdf115b-6af5-4bd5-858e-d567a698deb5

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PreparedWanted
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Schedule
import Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_QueryBudget
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedQueryBudget_y_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedQueryBudget_y_lt_one
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedQueryBudget_cut_scale
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_codes_length_gibbs
import Theorems.Thm_ThreeSum_TernaryNearBankEnumeration_codes_length_gibbs
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_codes_length_gibbs
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
theorem _root_.solution (m : ℕ) :
    ((WeightedAddresses.codes (fixedLength m) (bankCut m)).length : ℝ)≤
      exp ((fixedLength m : ℝ)*Bn) := by
  have hy := y_pos
  have ha : 0<bankArg := by unfold bankArg; positivity
  have hg := WeightedBankEnumeration.codes_length_gibbs (fixedLength m) (bankCut m) yRoot y_pos.le y_lt_one.le
  have he : bankArg^fixedLength m/yRoot^bankCut m=exp ((fixedLength m : ℝ)*Bn) := by
    have hp : 0<bankArg^fixedLength m/yRoot^bankCut m := by positivity
    rw [←exp_log hp,log_div (pow_pos ha _).ne' (pow_pos y_pos _).ne',log_pow,log_pow,cut_scale]
    unfold Bn
    congr 1
    ring
  change _*yRoot^bankCut m≤bankArg^fixedLength m at hg
  exact ((le_div_iff₀ (pow_pos y_pos _)).mpr hg).trans_eq he
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedQueryBudget
