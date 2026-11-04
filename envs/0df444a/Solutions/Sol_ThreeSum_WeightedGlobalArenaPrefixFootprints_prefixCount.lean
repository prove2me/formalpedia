-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPrefixFootprints.prefixCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T21:11:07.49978+00:00
-- url     : https://prove2.me/submissions/76596d91-1fe3-48e7-a3f3-31cc83b70681

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
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_Need_Ok_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_SolvedIn_mono
import Theorems.Thm_ThreeSum_LightWeightedGlobalDimensions_r_le
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
theorem _root_.solution {M : ℕ} (hM : 1<M) : Uniform M (fun _ _ j=>j) := by
  refine (inputN M |>.pow 2).mono ?_
  intro n U j hj
  exact hj.trans (LightWeightedGlobalDimensions.r_le hM n)
end ThreeSum.WeightedGlobalArenaPrefixFootprints
