-- Prove2me | solution 1 for ThreeSum.WeightedGlobalMomentChannelResources.score_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:52:31.258129+00:00
-- url     : https://prove2.me/submissions/6f2412bf-37cf-45cf-b0d5-53fab33ee155

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryMomentDetectorResources
import Definitions.Def_Submission_Weighted_Global_TernaryPhysicalPairWordBounds
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
import Definitions.Def_Submission_Weighted_Global_TernaryMomentChannelResources
import Theorems.Thm_ThreeSum_LightTernaryMomentChannels_left_bound
import Theorems.Thm_ThreeSum_LightTernaryMomentChannels_right_bound
import Theorems.Thm_ThreeSum_WeightedGlobalMomentWeightBounds_left_bound
import Theorems.Thm_ThreeSum_WeightedGlobalMomentWeightBounds_right_bound
import Theorems.Thm_ThreeSum_WeightedGlobalPhysicalPairWordBounds_weighted_abs_le_caps


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalMomentChannelResources
open WeightedGlobalMomentWeightBounds WeightedGlobalNativeMomentBounds StageBounds
namespace ThreeSum.WeightedGlobalMomentChannelResources
theorem _root_.solution {N B U K k j : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (left right : ℕ→ℤ) (hpairs : pairBound S*2^N≤B)
    (hleft : ∀ i<S.left.NL, |left i|≤(U : ℤ))
    (hright : ∀ i<S.right.NL, |right i|≤(U : ℤ)) (hk : k≤K) (hj : j≤k) (i : ℕ) :
    |LightWeightedGlobalMomentChannelFactory.score S left right k j i|≤(scoreBound B U K : ℤ) := by
  have hs := WeightedGlobalPhysicalPairWordBounds.weighted_abs_le_caps S
    (LightWeightedGlobalMomentChannelFactory.leftWeights k j left)
    (LightWeightedGlobalMomentChannelFactory.rightWeights k j right) i
    (fun a ha => left_bound (left a) (hleft a ha) hk hj)
    (fun a ha => right_bound (right a) (hright a ha) hk)
  have hm := Nat.mul_le_mul_right (rightBound U K)
    (Nat.mul_le_mul_right (leftBound U K) hpairs)
  exact hs.trans (by exact_mod_cast hm)
end ThreeSum.WeightedGlobalMomentChannelResources
