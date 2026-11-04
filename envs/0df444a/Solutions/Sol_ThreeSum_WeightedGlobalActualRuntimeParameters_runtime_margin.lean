-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualRuntimeParameters.runtime_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:27:12.721962+00:00
-- url     : https://prove2.me/submissions/19d73cdb-77bc-4f7b-8ae5-260b03266354

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualSeedRuntime
import Definitions.Def_Submission_Weighted_Global_TernarySignedParameters
import Definitions.Def_Submission_Weighted_Global_TernaryActualRuntimeParameters
import Theorems.Thm_ThreeSum_WeightedGlobalActualPrefixRuntime_full_exponent_lt


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalActualRuntimeParameters
open WeightedGlobalActualPrefixRuntime WeightedGlobalActualSeedRuntime WeightedGlobalOversizePrime
open WeightedGlobalOversizeOverhead WeightedGlobalOversizeRates WeightedGlobalSignedPadding
set_option maxHeartbeats 2000000
namespace ThreeSum.WeightedGlobalActualRuntimeParameters
theorem _root_.solution {K m : ℕ} (hK : 100000000000000000000≤K) (c d : ℕ)
    (hgood : GoodBlock K m)
    (hover : overheadCharge (selectedMoment K) c d m<microAllowance K) :
    fullExponent K (selectedMoment K) c d m+microAllowance K+(1/1250000000:ℝ)<
      WeightedGlobalParameters.targetExponent:=by
  have ht:=full_exponent_lt hK c d hgood hover
  have hk : (100000000000000000000:ℝ)≤K:=by exact_mod_cast hK
  have hp : (0:ℝ)<K:=by linarith
  have hμ : microAllowance K<(1/1250000000:ℝ):=by
    unfold microAllowance
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  norm_num [WeightedGlobalCountFrontendBudget.frontendExponent,WeightedGlobalParameters.targetExponent] at ht ⊢
  linarith
end ThreeSum.WeightedGlobalActualRuntimeParameters
