-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixSetupResources.exponent_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:23:53.158537+00:00
-- url     : https://prove2.me/submissions/df8cd559-2d05-4fe9-a5af-38e44cad0201

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_FrontendResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixSetupResources

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixSetupResources
open Light LightWeightedGlobalPrefixSetup StageBounds WeightedGlobalCoverScale
open WeightedGlobalFrontendResources
open Filter
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixSetupResources
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
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixSetupResources
