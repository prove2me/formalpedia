-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentChannelResources.score_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:44:44.438489+00:00
-- url     : https://prove2.me/submissions/cf07452b-6514-4918-835e-a077258b34a4

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentDetectorResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPhysicalPairWordBounds
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentChannelResources
import Theorems.Thm_ThreeSum_LightTernaryMomentChannels_left_bound
import Theorems.Thm_ThreeSum_LightTernaryMomentChannels_right_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalMomentWeightBounds_left_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalMomentWeightBounds_right_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPhysicalPairWordBounds_weighted_abs_le_caps


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentChannelResources
open WeightedGlobalMomentWeightBounds WeightedGlobalNativeMomentBounds StageBounds
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentChannelResources
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
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentChannelResources
