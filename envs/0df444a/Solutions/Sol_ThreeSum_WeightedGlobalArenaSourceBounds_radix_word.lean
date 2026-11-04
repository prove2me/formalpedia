-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaSourceBounds.radix_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T21:05:35.15481+00:00
-- url     : https://prove2.me/submissions/f19a4464-89e8-4623-8888-8a11151b447c

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixFootprints
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceBounds

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters LightTernarySourceHost WeightedGlobalNativeCompleteFrontend
variable {p m F r : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaSourceBounds
theorem _root_.solution (P j : ℕ) :
    LightRadixKeys.word P P j=P+P*P*(P+1)^j+P+1 := by
  unfold LightRadixKeys.word LightRadixRows.word
  ring
end ThreeSum.WeightedGlobalArenaSourceBounds
