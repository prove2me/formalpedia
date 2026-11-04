-- Prove2me | solution 1 for ThreeSum.WeightedGlobalDimensionBounds.query_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:04:55.989361+00:00
-- url     : https://prove2.me/submissions/ae2f7a55-0419-4850-a070-43f9fa9b27e3

import Definitions.Def_Submission_Weighted_GlobalParameters
import Definitions.Def_Submission_Weighted_GlobalLocalParameters
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_QueryBudget
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Theorems.Thm_ThreeSum_WeightedGlobalDimensionBounds_deficit_schedule
import Theorems.Thm_ThreeSum_WeightedGlobalDimensionBounds_near_pos
import Theorems.Thm_ThreeSum_WeightedQueryBudget_near_card_bound
import Theorems.Thm_ThreeSum_WeightedQueryBudget_z_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalDimensionBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalBank WeightedGlobalParameters
namespace ThreeSum.WeightedGlobalDimensionBounds
theorem _root_.solution {m j : ℕ} (Q : TritWord (fixedLength (j*m)))
    (hQ : HasType Q (fixedPi (j*m))) :
    Real.log ((nearWords Q (queryDeficit m j)).card : ℝ)≤
      (fixedLength (j*m) : ℝ)*Real.log 2*queryEntropy-1024*Real.log z := by
  have hc : 0<((nearWords Q (queryDeficit m j)).card : ℝ) := by exact_mod_cast near_pos Q _
  have hg := WeightedQueryBudget.near_card_bound (m := j*m) Q hQ
  have hg' : ((nearWords Q (queryDeficit m j)).card : ℝ)≤WeightedQueryBudget.envelope (j*m) := by
    rw [deficit_schedule]
    exact hg
  have hh := Real.log_le_log hc hg'
  rw [WeightedQueryBudget.envelope,Real.log_div (Real.exp_pos _).ne'
    (pow_pos WeightedQueryBudget.z_pos _).ne',Real.log_exp,Real.log_pow] at hh
  have he : (fixedLength (j*m) : ℝ)*Real.log 2*queryEntropy=
      (fixedLength (j*m) : ℝ)*WeightedCacheParameters.Qn := by
    unfold queryEntropy
    field_simp
  rw [he]
  exact hh
end ThreeSum.WeightedGlobalDimensionBounds
