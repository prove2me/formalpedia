-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCountFrontendBudget.principal_exponent_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:22:26.088662+00:00
-- url     : https://prove2.me/submissions/0e342c77-90c8-4cad-9907-7c93420729c9

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PreparedBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_CountFrontend
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_CountFrontendBudget

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCountFrontendBudget
open Filter Real Asymptotics
open TernaryJointType WeightedGlobalBank WeightedGlobalParameters WeightedGlobalDimensionBounds
open WeightedGlobalEntropyRates WeightedGlobalLocalParameters WeightedGlobalCoverScale WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalCoverCapParameters
open WeightedGlobalOversizeOverhead WeightedGlobalOversizeDimensions WeightedGlobalPrincipalDimensions
open LightWeightedNearPair
open scoped Topology
set_option maxHeartbeats 5000000
set_option maxRecDepth 16000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCountFrontendBudget
theorem _root_.solution {K m : ℕ} (hK : 100000000000000000000≤K) (c d : ℕ)
    (hgood : GoodBlock K m)
    (hover : overheadCharge (selectedMoment K) c d m<microAllowance K) :
    principalExponent K (selectedMoment K) c d m<frontendExponent := by
  have hmax : max (WeightedGlobalOversizeRates.bankCharge K m) (WeightedGlobalOversizeRates.queryCharge K m)<softCertificate :=
    max_lt hgood.2.1 hgood.2.2.1
  have hkr : (100000000000000000000 : ℝ)≤K := by exact_mod_cast hK
  have hkp : (0 : ℝ)<K := by linarith
  have hmicro : microAllowance K<(1/50000000000000 : ℝ) := by
    unfold microAllowance
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  have hsum := add_lt_add hmax hover
  have hbound : softCertificate+microAllowance K<frontendExponent := by
    norm_num [softCertificate,frontendExponent]
    linarith
  exact hsum.trans hbound
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCountFrontendBudget
