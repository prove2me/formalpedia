-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalEntropyRates.denominator_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:25:30.488477+00:00
-- url     : https://prove2.me/submissions/bdf13ae6-91f0-460a-aa87-90bf8815c02b

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryEntropyRates
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_log_two_pos


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters WeightedGlobalCoverScale
set_option maxRecDepth 10000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalEntropyRates
theorem _root_.solution {m : ℕ} (hm : 0 < m) :
    0 < (fixedLength m : ℝ)*Real.log 2 := by
  have hL : 0 < fixedLength m := by unfold fixedLength; positivity
  exact mul_pos (by exact_mod_cast hL) WeightedGlobalParameters.log_two_pos
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalEntropyRates
