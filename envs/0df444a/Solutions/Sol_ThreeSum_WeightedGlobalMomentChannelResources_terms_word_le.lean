-- Prove2me | solution 1 for ThreeSum.WeightedGlobalMomentChannelResources.terms_word_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:36:13.295282+00:00
-- url     : https://prove2.me/submissions/f123630f-3d5b-46e7-af5b-51957d37a629

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryMomentDetectorResources
import Definitions.Def_Submission_Weighted_Global_TernaryPhysicalPairWordBounds
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
import Definitions.Def_Submission_Weighted_Global_TernaryMomentChannelResources

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalMomentChannelResources
open WeightedGlobalMomentWeightBounds WeightedGlobalNativeMomentBounds StageBounds
namespace ThreeSum.WeightedGlobalMomentChannelResources
theorem _root_.solution (B U K : ℕ) : K+1≤(need B U K).word := by
  have hc : K+1≤coefficient K := by unfold coefficient; omega
  have hB : coefficient K≤coefficient K*(B+1) := Nat.le_mul_of_pos_right _ (by omega)
  exact (hc.trans hB).trans (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by omega)))
end ThreeSum.WeightedGlobalMomentChannelResources
