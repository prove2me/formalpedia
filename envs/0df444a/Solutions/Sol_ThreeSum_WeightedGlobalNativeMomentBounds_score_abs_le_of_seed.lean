-- Prove2me | solution 1 for ThreeSum.WeightedGlobalNativeMomentBounds.score_abs_le_of_seed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:42:34.286202+00:00
-- url     : https://prove2.me/submissions/135f8e40-b872-461e-8c47-5c0855f1832b

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
import Theorems.Thm_ThreeSum_WeightedGlobalNativeMomentBounds_score_abs_le

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativeMomentBounds
open Finset TernaryJointType WeightedGlobalNativePairMoments
open scoped BigOperators
namespace ThreeSum.WeightedGlobalNativeMomentBounds
theorem _root_.solution {N d boundary : ℕ} {lim : Light.Limits}
    (S : WeightedSourceCountExecutionFactory.Setup N) (μ : ℕ→ℤ) (B C : ℕ→ℤ) (k j i : ℕ)
    (H : WeightedSourceCountExecutionFactory.Seed S lim d boundary μ
      (LightWeightedGlobalMomentChannelFactory.leftWeights k j B)
      (LightWeightedGlobalMomentChannelFactory.rightWeights k j C)) :
    |LightWeightedGlobalMomentChannelFactory.score S B C k j i|≤(scoreBound S : ℤ) :=
  score_abs_le S B C k j i H.left.hweightBound H.right.hweightBound
end ThreeSum.WeightedGlobalNativeMomentBounds
