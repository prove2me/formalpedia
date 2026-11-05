-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalDimensionBounds.query_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:21:06.19319+00:00
-- url     : https://prove2.me/submissions/50168d44-5365-415f-b353-53e6c8fbd2b3

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalLocalParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_QueryBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_DimensionBounds
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalDimensionBounds_deficit_schedule
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalDimensionBounds_near_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedQueryBudget_near_card_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedQueryBudget_z_pos


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalDimensionBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalBank WeightedGlobalParameters
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalDimensionBounds
theorem _root_.solution {m j : ℕ} (Q : TritWord (fixedLength (j*m)))
    (hQ : HasType Q (fixedPi (j*m))) :
    Real.log ((nearWords Q (queryDeficit m j)).card : ℝ)≤
      (fixedLength (j*m) : ℝ)*Real.log 2*queryEntropy-2739*Real.log z := by
  have hc : 0<((nearWords Q (queryDeficit m j)).card : ℝ) := by exact_mod_cast near_pos Q _
  have hg := WeightedQueryBudget.near_card_bound (m := j*m) Q hQ
  have hg' : ((nearWords Q (queryDeficit m j)).card : ℝ)≤WeightedQueryBudget.envelope (j*m) := by
    rw [deficit_schedule]
    exact hg
  have hh := Real.log_le_log hc hg'
  rw [WeightedQueryBudget.envelope,Real.log_div (Real.exp_pos _).ne'
    (pow_pos WeightedQueryBudget.z_pos _).ne',Real.log_exp,Real.log_pow] at hh
  have he : (fixedLength (j*m) : ℝ)*Real.log 2*queryEntropy=
      (fixedLength (j*m) : ℝ)*WeightedCacheParameters_e1ae71d.Qn := by
    unfold queryEntropy
    field_simp
  rw [he]
  exact hh
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalDimensionBounds
