-- Prove2me | solution 1 for ThreeSum.WeightedGlobalNativeTensorScore.score_eq_original_tensor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:07:26.218209+00:00
-- url     : https://prove2.me/submissions/276b47ff-137b-43c3-a957-0c3e70a62c84

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryScaled
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTensorScore
import Theorems.Thm_ThreeSum_WeightedGlobalNativeTensorScore_packed_digits
import Theorems.Thm_ThreeSum_TernaryPhysicalSources_convolution_histograms
import Theorems.Thm_ThreeSum_TernaryPhysicalTensorChannels_fourth_tensor_on_physical_records
import Theorems.Thm_ThreeSum_TernaryWeightedPhysicalSources_convolution_histograms


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativeTensorScore
open TernaryJointType WeightedGlobalNativePairMoments
open LightWeightedGlobalTensorFactory LightTernaryPairedPolynomial
open scoped BigOperators
set_option maxHeartbeats 1500000
namespace ThreeSum.WeightedGlobalNativeTensorScore
theorem _root_.solution {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (J : ℕ) (L R : ℕ→ℕ→ℤ) (i : ℕ) (a b c d : Fin (J+2)) :
    score S J L R i (tensorIndex (J+2) a.val b.val c.val d.val)=
      TernaryConvolution.factorial (S.front.Q i)*
        TernaryPairedTensor.tensor (originalLeft S J L i) (originalRight S J R i) a b c d := by
  have hdigit := packed_digits (by omega : 0<J+2) a.isLt b.isLt c.isLt d.isLt
  have hphysical := TernaryPhysicalTensorChannels.fourth_tensor_on_physical_records
    (leftSet S i) (rightSet S i) (leftWord S) (rightWord S)
    (fun pair (a : Fin (J+2)) => L pair.1 a.val)
    (fun pair (a : Fin (J+2)) => R pair.1 a.val) a b c d (S.front.Q i)
  rw [TernaryWeightedPhysicalSources.convolution_histograms] at hphysical
  unfold score leftWeights rightWeights LightWeightedGlobalTensorDriver.digit
  rw [hdigit.1,hdigit.2.1,hdigit.2.2.1,hdigit.2.2.2]
  exact congrArg (fun z => TernaryConvolution.factorial (S.front.Q i)*z) hphysical
end ThreeSum.WeightedGlobalNativeTensorScore
