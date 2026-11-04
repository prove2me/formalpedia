-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaSourceControlBudget.upperWord_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:10:54.644661+00:00
-- url     : https://prove2.me/submissions/996393bf-bb82-4867-8c58-098c46c3f9e5

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceControls
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceControlBudget

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceControlBudget
open Light WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceControls
open WeightedGlobalArenaPairMass WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
open WeightedGlobalCoverGoodMaps StageBounds
variable {p m F r : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaSourceControlBudget
theorem _root_.solution {m p F R r s n a w v : ℕ}
    (hp : 1≤p) (hF : 1≤F) (hR : 1≤R) (hr : r≤s) (hn : n≤a) (hw : w≤v) :
    upperWord m p F R r n w≤upperWord m p F R s a v := by
  have hfour : 1≤4^fixedLength m := Nat.one_le_pow _ _ (by decide)
  unfold upperWord baseWord weightCoefficient LightRadixKeys.word LightRadixRows.word
    LightSourceResidues.word N
  gcongr <;> omega
end ThreeSum.WeightedGlobalArenaSourceControlBudget
