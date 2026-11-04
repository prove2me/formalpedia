-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPrefixFootprints.alphabet_final
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T21:07:54.551476+00:00
-- url     : https://prove2.me/submissions/9e14a4f8-8820-4266-950c-8f6c32728559

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
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixFootprints_alphabet

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixFootprints
open WeightedGlobalArenaLayout WeightedGlobalArenaPairMass WeightedGlobalSignedPadding
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
attribute [local semireducible] Uniform

namespace ThreeSum.WeightedGlobalArenaPrefixFootprints
theorem _root_.solution {M : ℕ} (hM : 1<M) (A : ℕ) :
    Uniform M (fun n _ _=>A^(Nat.clog M (n^2))) := by
  obtain ⟨D,E,h⟩ := alphabet hM A
  exact ⟨D,E,fun n U j _=>h n U _ le_rfl⟩
end ThreeSum.WeightedGlobalArenaPrefixFootprints
