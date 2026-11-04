-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPrefixFootprints.digits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T21:11:04.62483+00:00
-- url     : https://prove2.me/submissions/b49cfa1d-2a2b-4fdf-a108-95ddd1e7b92a

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPairMass
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensionsBudget
import Definitions.Def_Submission_ThreeSum_LightTernaryInitialBudgets
import Definitions.Def_Submission_Weighted_Global_TernaryMomentWeightBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCapacity
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotential
import Definitions.Def_Submission_Weighted_Global_TernaryMomentChannelResources
import Definitions.Def_Submission_ThreeSum_LightTernaryAppendKeys
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixFootprints
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixFootprints_Uniform_mono
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixFootprints_inputN
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixFootprints_inputU
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_Need_Ok_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_SolvedIn_mono
import Theorems.Thm_ThreeSum_LightWeightedGlobalDimensions_J_le
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_const
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mul
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_pow


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixFootprints
open WeightedGlobalArenaLayout WeightedGlobalArenaPairMass WeightedGlobalSignedPadding
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
attribute [local semireducible] Uniform

namespace ThreeSum.WeightedGlobalArenaPrefixFootprints
theorem _root_.solution {M b : ℕ} (hM : 1<M) (hb : 1<b) :
    Uniform M (fun n U _=>LightWeightedGlobalDimensions.J M b n U) := by
  refine (((inputN M |>.pow 2).add ((Uniform.const M 4).mul (inputU M))).add (Uniform.const M 3)).mono ?_
  intro n U j hj
  exact LightWeightedGlobalDimensions.J_le hM hb n U
end ThreeSum.WeightedGlobalArenaPrefixFootprints
