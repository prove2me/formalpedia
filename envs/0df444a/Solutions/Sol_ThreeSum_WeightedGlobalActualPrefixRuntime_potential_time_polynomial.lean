-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualPrefixRuntime.potential_time_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T17:18:20.438784+00:00
-- url     : https://prove2.me/submissions/2c5e20f0-2b78-4915-b698-a87687e39492

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernarySourceHostBudget
import Definitions.Def_Submission_ThreeSum_TernaryWantedDictionaryFiber
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_Submission_Weighted_Global_TernaryMomentReporterBudget
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedControllerBudget
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScoreFactory
import Definitions.Def_Submission_Weighted_Global_TernarySignedPreparationBudget
import Definitions.Def_Submission_Weighted_Global_TernaryExtensionBudget
import Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalActualPrefixRuntime
open Light Real Filter Asymptotics
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend
open WeightedGlobalEntropyRates WeightedGlobalDimensionBounds WeightedGlobalOversizePrime
open WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale
open scoped BigOperators Topology
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable
namespace ThreeSum.WeightedGlobalActualPrefixRuntime
theorem _root_.solution (K Λ : ℕ) (hΛ : 1≤Λ) :
    LightTernaryPairedPotential.time K Λ≤
      potentialCoefficient K*Λ^(2*TernaryPairedColumnEnumeration.width K) :=by
  let w:=TernaryPairedColumnEnumeration.width K
  have hpow : Λ^w≤Λ^(2*w):=Nat.pow_le_pow_right hΛ (by omega)
  have h1 : 1≤Λ^(2*w):=Nat.one_le_pow _ _ hΛ
  have hlinear:=Nat.mul_le_mul_left (240*w+LightTernaryPairedPolynomial.time K+306) hpow
  have hconst:=Nat.mul_le_mul_left (powTableTime (w+1)+300) h1
  unfold LightTernaryPairedPotential.time LightWeightRow.time LightRadixDigit.time potentialCoefficient
  change _≤(powTableTime (w+1)+280*w+LightTernaryPairedPolynomial.time K+700)*Λ^(2*w)
  rw [show Λ^(2*w)=(Λ^w)^2 by rw [Nat.mul_comm 2 w,pow_mul]] at hlinear hconst ⊢
  nlinarith only [hlinear,hconst]
end ThreeSum.WeightedGlobalActualPrefixRuntime
