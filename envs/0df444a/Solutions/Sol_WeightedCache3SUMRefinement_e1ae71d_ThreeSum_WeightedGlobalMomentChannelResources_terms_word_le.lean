-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentChannelResources.terms_word_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:34:43.861259+00:00
-- url     : https://prove2.me/submissions/9e67bca2-5b82-4f0b-b05c-c6efe06f4e2d

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentDetectorResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPhysicalPairWordBounds
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentChannelResources

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentChannelResources
open WeightedGlobalMomentWeightBounds WeightedGlobalNativeMomentBounds StageBounds
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentChannelResources
theorem _root_.solution (B U K : ℕ) : K+1≤(need B U K).word := by
  have hc : K+1≤coefficient K := by unfold coefficient; omega
  have hB : coefficient K≤coefficient K*(B+1) := Nat.le_mul_of_pos_right _ (by omega)
  exact (hc.trans hB).trans (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by omega)))
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentChannelResources
