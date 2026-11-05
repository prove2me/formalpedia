-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceControlBudget.upperWord_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T13:11:25.947787+00:00
-- url     : https://prove2.me/submissions/73a1273b-669d-4e82-bed4-3c4afeffb3ad

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceControls
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceControlBudget

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceControlBudget
open Light WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceControls
open WeightedGlobalArenaPairMass WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
open WeightedGlobalCoverGoodMaps StageBounds
variable {p m F r : ℕ} [Fact p.Prime]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceControlBudget
theorem _root_.solution {m p F R r s n a w v : ℕ}
    (hp : 1≤p) (hF : 1≤F) (hR : 1≤R) (hr : r≤s) (hn : n≤a) (hw : w≤v) :
    upperWord m p F R r n w≤upperWord m p F R s a v := by
  have hfour : 1≤4^fixedLength m := Nat.one_le_pow _ _ (by decide)
  unfold upperWord baseWord weightCoefficient LightRadixKeys.word LightRadixRows.word
    LightSourceResidues.word N
  gcongr <;> omega
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceControlBudget
