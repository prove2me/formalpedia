-- Prove2me | solution 1 for ThreeSum.WeightedGlobalSignedPreparationBudget.digitConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:31:07.88287+00:00
-- url     : https://prove2.me/submissions/f98991dc-3efc-447e-b225-bd60271ae51b

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernarySignedParameters
import Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryApply
import Definitions.Def_Submission_Weighted_Global_TernarySignedPreparationBudget
import Theorems.Thm_ThreeSum_WeightedGlobalPrincipalDimensions_output_log_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalSignedPreparationBudget
open Filter Real Asymptotics WeightedGlobalSignedPadding WeightedGlobalCoverScale
open WeightedGlobalPrincipalDimensions WeightedGlobalLocalParameters WeightedGlobalParameters
open scoped Topology
namespace ThreeSum.WeightedGlobalSignedPreparationBudget
theorem _root_.solution {m b : ℕ} (hm : 0<m) (hb : 1<b) {κ : ℝ} (hκ : 0≤κ) :
    0<digitConstant m b κ := by
  have hLb := Real.log_pos (by exact_mod_cast hb : (1 : ℝ)<b)
  have hLM := output_log_pos hm
  have h5 : 0<Real.log 5 := Real.log_pos (by norm_num)
  unfold digitConstant
  positivity
end ThreeSum.WeightedGlobalSignedPreparationBudget
