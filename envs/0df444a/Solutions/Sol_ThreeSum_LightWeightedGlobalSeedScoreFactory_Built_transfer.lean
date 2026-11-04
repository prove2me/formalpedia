-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalSeedScoreFactory.Built.transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:47:24.143199+00:00
-- url     : https://prove2.me/submissions/7fecd9fa-1fdc-4190-ba0c-748886f6ea67

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScore
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalDigitSpan
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchCount
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryScaled
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTensorScore
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScoreFactory
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScoreFactory_BuiltO_transfer
import Theorems.Thm_Light_Seg_of_kept
import Theorems.Thm_ThreeSum_LightTernaryPreparedState_Snapshot_transfer
import Theorems.Thm_ThreeSum_LightWeightedPreparedState_Snapshot_transfer


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalSeedScoreFactory
open Light
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits}
namespace ThreeSum.LightWeightedGlobalSeedScoreFactory
namespace Built
theorem _root_.solution {C : Config} {D : Data C} {depth R S cap V cutoff : ℕ}
    {raws : List ℤ} {words maps : List ℕ} {μ ν ξ : ℕ → ℤ}
    (G : AppendGuard C D lim depth μ) (W : WantedGuard C D lim depth R S cap V raws words maps μ)
    (H : Built C D R S raws words maps μ ν) (K : Kept ν ξ cutoff)
    (hcut : C.wanted+(D.wantedRows R S raws words maps).length≤cutoff) :
    Built C D R S raws words maps μ ξ := by
  exact ⟨H.1.transfer G K (by have := W.targetEnd; omega),H.2.of_kept K hcut⟩
end Built
end ThreeSum.LightWeightedGlobalSeedScoreFactory
