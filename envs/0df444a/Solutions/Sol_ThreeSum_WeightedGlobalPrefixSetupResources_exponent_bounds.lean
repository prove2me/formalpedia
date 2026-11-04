-- Prove2me | solution 1 for ThreeSum.WeightedGlobalPrefixSetupResources.exponent_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:32:07.377851+00:00
-- url     : https://prove2.me/submissions/6219fa5e-4634-4890-a5d4-44cbef7a2c65

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
import Definitions.Def_Submission_Weighted_Global_FrontendResources
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixSetupResources

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrefixSetupResources
open Light LightWeightedGlobalPrefixSetup StageBounds WeightedGlobalCoverScale
open WeightedGlobalFrontendResources
open Filter
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000
namespace ThreeSum.WeightedGlobalPrefixSetupResources
theorem _root_.solution (m F : ℕ) :
    0≤ exponent m F ∧
    2*Real.log (F+1:ℕ)/Real.log (outputSize m:ℝ)≤ exponent m F ∧
    2*Real.log (4^WeightedGlobalLocalParameters.fixedLength m:ℕ)/Real.log (outputSize m:ℝ)≤ exponent m F := by
  unfold exponent
  constructor
  · positivity
  constructor <;> linarith [le_abs_self (2*Real.log (F+1:ℕ)/Real.log (outputSize m:ℝ)),
    le_abs_self (2*Real.log (4^WeightedGlobalLocalParameters.fixedLength m:ℕ)/Real.log (outputSize m:ℝ)),
    abs_nonneg (2*Real.log (F+1:ℕ)/Real.log (outputSize m:ℝ)),
    abs_nonneg (2*Real.log (4^WeightedGlobalLocalParameters.fixedLength m:ℕ)/Real.log (outputSize m:ℝ))]
end ThreeSum.WeightedGlobalPrefixSetupResources
