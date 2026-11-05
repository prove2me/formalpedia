-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalUniformQueryTime.envelope_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T14:43:17.496165+00:00
-- url     : https://prove2.me/submissions/960682f4-78ab-41c5-a7d4-2b170c5c98db

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFrontBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaAllocation
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryUniformQueryTime
import Theorems.Thm_ThreeSum_TernaryParameters_analytic_admissibility
import Theorems.Thm_ThreeSum_TernaryParameters_gibbs_parameters
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_analytic_admissibility
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_gibbs_parameters


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalUniformQueryTime
open WeightedGlobalArenaSourceSetup WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalActualPrefixRuntime WeightedGlobalArenaAllocation WeightedGlobalArenaPrefixFootprints
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalUniformQueryTime
theorem _root_.solution {j R : ℕ} (hj : j≤R) :
    WeightedGlobalCountFrontendBudget.envelope m j≤WeightedGlobalCountFrontendBudget.envelope m R := by
  have hlen : fixedLength (j*m)≤fixedLength (R*m) := by
    unfold fixedLength
    gcongr
  have hlog : 0≤Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  have hent : 0≤WeightedGlobalParameters.queryEntropy := WeightedGlobalParameters.analytic_admissibility.2.1.le
  unfold WeightedGlobalCountFrontendBudget.envelope
  apply div_le_div_of_nonneg_right _ (pow_pos WeightedGlobalParameters.gibbs_parameters.2.2.1 2739).le
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hlen) hlog) hent
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalUniformQueryTime
