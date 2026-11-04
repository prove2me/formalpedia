-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T20:55:43.189418+00:00
-- url     : https://prove2.me/submissions/1f9465b1-88fa-4733-a696-3a29a8c6c605

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

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixFootprints
open WeightedGlobalArenaLayout WeightedGlobalArenaPairMass WeightedGlobalSignedPadding
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
attribute [local semireducible] Uniform

namespace ThreeSum.WeightedGlobalArenaPrefixFootprints
namespace Uniform
theorem _root_.solution {M : ℕ} {f g : ℕ→ℕ→ℕ→ℕ}
    (hg : Uniform M g) (h : ∀ n U j, j≤Nat.clog M (n^2) → f n U j≤g n U j) : Uniform M f := by
  obtain ⟨D,E,hg⟩:=hg
  exact ⟨D,E,fun n U j hj=>(h n U j hj).trans (hg n U j hj)⟩
end Uniform
end ThreeSum.WeightedGlobalArenaPrefixFootprints
