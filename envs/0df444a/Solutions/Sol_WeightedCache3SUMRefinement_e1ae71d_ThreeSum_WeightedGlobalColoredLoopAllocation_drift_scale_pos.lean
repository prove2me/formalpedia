-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopAllocation.drift_scale_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:13:57.91056+00:00
-- url     : https://prove2.me/submissions/b730bbb0-15cc-4ce3-9746-da0815e61de1

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopAllocation
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalConcreteProfile_Profile_F_gt_one


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopAllocation
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalColoredLoopSetup
open WeightedGlobalArenaPrefixFootprints
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {κ : ℕ}
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopAllocation
theorem _root_.solution (P : Profile κ) : 1≤P.drift*P.scale := by
  have hF:=P.F_gt_one
  have hM:=P.M_gt_one
  have hR : 0<WeightedGlobalGoodOutputCatalog.Rbar P.m := by
    unfold WeightedGlobalGoodOutputCatalog.Rbar
    positivity
  have hs : 0<P.scale := by unfold Profile.scale;positivity
  have hd : 0<P.drift := by unfold Profile.drift;positivity
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopAllocation
