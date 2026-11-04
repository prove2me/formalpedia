-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPrimitiveBounds.append_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T21:29:21.546724+00:00
-- url     : https://prove2.me/submissions/85dd35c0-1df7-499c-8792-afe557e0a3ee

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedPrimitiveGuards
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrimitiveBounds

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrimitiveBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
open WeightedGlobalArenaSeedCandidate LightWeightedGlobalSeedScoreFactory
set_option maxHeartbeats 6000000
variable {p m F r : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaPrimitiveBounds
theorem _root_.solution {len p b power power' : ℕ} (hb : b≤p) (hp : power≤power') :
    LightTernaryAppendKeys.word len p b power≤LightTernaryAppendKeys.word len p p power' := by
  unfold LightTernaryAppendKeys.word LightSignedRowHash.word
  gcongr
end ThreeSum.WeightedGlobalArenaPrimitiveBounds
