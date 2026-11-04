-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaTensorBounds.tensor_words_le_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T21:09:58.242168+00:00
-- url     : https://prove2.me/submissions/153e65f4-259e-438a-b2e1-1c55aa34fce6

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFrontBounds
import Definitions.Def_Submission_Weighted_Global_TernaryTensorWordResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTensorBounds
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixFootprints_Numbers_sum_list


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaTensorBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds
open WeightedGlobalArenaFrontBounds WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
open WeightedGlobalNativeCompleteFrontend WeightedGlobalNativeMomentBounds
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
namespace ThreeSum.WeightedGlobalArenaTensorBounds
theorem _root_.solution (maps : Fin F→Weight m p) (τ cap M b K H drift scale n U j : ℕ) :
    (numbers maps τ cap M b K H drift scale n U j).potentialWord+
      (numbers maps τ cap M b K H drift scale n U j).tensorWord≤
      total maps τ cap M b K H drift scale n U j := by
  unfold total
  generalize numbers maps τ cap M b K H drift scale n U j=A
  change A.potentialWord+A.tensorWord≤A.list.sum
  rw [Numbers.sum_list]
  omega
end ThreeSum.WeightedGlobalArenaTensorBounds
