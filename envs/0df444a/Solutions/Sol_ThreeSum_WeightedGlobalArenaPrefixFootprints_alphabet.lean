-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPrefixFootprints.alphabet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T20:57:43.192914+00:00
-- url     : https://prove2.me/submissions/b2365225-9a6c-4e95-b8e7-0f0cff6be798

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
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPairMass_fixed_pow_clog


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixFootprints
open WeightedGlobalArenaLayout WeightedGlobalArenaPairMass WeightedGlobalSignedPadding
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
attribute [local semireducible] Uniform

namespace ThreeSum.WeightedGlobalArenaPrefixFootprints
theorem _root_.solution {M : ℕ} (hM : 1<M) (A : ℕ) : Uniform M (fun _ _ j=>A^j) := by
  refine ⟨M^(A+1),2*(A+1),fun n U j hj=>?_⟩
  have hh := (Nat.pow_le_pow_left (Nat.le_succ A) j).trans
    ((Nat.pow_le_pow_right (by omega : 1≤A+1) hj).trans (fixed_pow_clog M (A+1) n hM))
  exact hh.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : n+1≤n+U+1) _))
end ThreeSum.WeightedGlobalArenaPrefixFootprints
