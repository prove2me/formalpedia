-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCountFrontendBudget.envelope_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:25:30.614906+00:00
-- url     : https://prove2.me/submissions/6899f8ad-6bdf-4130-8699-7181d107bcba

import Definitions.Def_Submission_Weighted_PreparedBudget
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_Submission_Weighted_Global_CountFrontendBudget
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_analytic_admissibility
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_gibbs_parameters
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_log_two_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCountFrontendBudget
open Filter Real Asymptotics
open TernaryJointType WeightedGlobalBank WeightedGlobalParameters WeightedGlobalDimensionBounds
open WeightedGlobalEntropyRates WeightedGlobalLocalParameters WeightedGlobalCoverScale WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalCoverCapParameters
open WeightedGlobalOversizeOverhead WeightedGlobalOversizeDimensions WeightedGlobalPrincipalDimensions
open LightWeightedNearPair
open scoped Topology
set_option maxHeartbeats 5000000
set_option maxRecDepth 16000
namespace ThreeSum.WeightedGlobalCountFrontendBudget
theorem _root_.solution (m j : ℕ) : 1≤envelope m j := by
  have hz := gibbs_parameters.2.2.1
  have hq : 0≤queryEntropy := analytic_admissibility.2.1.le
  have hE : 1≤Real.exp ((fixedLength (j*m) : ℝ)*Real.log 2*queryEntropy) :=
    Real.one_le_exp_iff.mpr (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) log_two_pos.le) hq)
  have hp : z^1024≤1 := pow_le_one₀ hz.le gibbs_parameters.2.2.2.le
  unfold envelope
  exact (one_le_div (pow_pos hz _)).mpr (hp.trans hE)
end ThreeSum.WeightedGlobalCountFrontendBudget
