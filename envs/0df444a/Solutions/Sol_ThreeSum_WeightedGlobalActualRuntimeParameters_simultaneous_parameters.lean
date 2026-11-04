-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualRuntimeParameters.simultaneous_parameters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:46:33.694526+00:00
-- url     : https://prove2.me/submissions/ab3fdfd2-035c-44da-9d66-cc419efd06a8

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualSeedRuntime
import Definitions.Def_Submission_Weighted_Global_TernarySignedParameters
import Definitions.Def_Submission_Weighted_Global_TernaryActualRuntimeParameters
import Theorems.Thm_ThreeSum_WeightedGlobalActualRuntimeParameters_runtime_margin
import Theorems.Thm_ThreeSum_WeightedGlobalPairedCollisionRate_simultaneous_parameters
import Theorems.Thm_ThreeSum_WeightedGlobalPairedFamilyMargin_simultaneous_parameters
import Theorems.Thm_ThreeSum_WeightedGlobalSignedParameters_simultaneous_parameters


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalActualRuntimeParameters
open WeightedGlobalActualPrefixRuntime WeightedGlobalActualSeedRuntime WeightedGlobalOversizePrime
open WeightedGlobalOversizeOverhead WeightedGlobalOversizeRates WeightedGlobalSignedPadding
set_option maxHeartbeats 2000000
namespace ThreeSum.WeightedGlobalActualRuntimeParameters
theorem _root_.solution {K : ℕ} (hK : 100000000000000000000≤K)
    {κ : ℝ} (hκ : 0≤κ) (c d N : ℕ) :
    ∃ t m : ℕ, 0<t ∧ N≤m ∧ GoodBlock K m ∧
      overheadCharge (selectedMoment K) c d m<microAllowance K ∧
      carryExponent m (2^t) κ<microAllowance K ∧
      (2*K).factorial*(2^t)^(2*K)<nativePrime K m ∧
      2*(2^t)<nativePrime K m ∧
      fullExponent K (selectedMoment K) c d m+microAllowance K+(1/1250000000:ℝ)<
        WeightedGlobalParameters.targetExponent:=by
  obtain ⟨t,m,ht,hN,hgood,hover,hcarry,hminor,hprime⟩:=
    WeightedGlobalSignedParameters.simultaneous_parameters hK hκ c d N
  exact ⟨t,m,ht,hN,hgood,hover,hcarry,hminor,hprime,runtime_margin hK c d hgood hover⟩
end ThreeSum.WeightedGlobalActualRuntimeParameters
