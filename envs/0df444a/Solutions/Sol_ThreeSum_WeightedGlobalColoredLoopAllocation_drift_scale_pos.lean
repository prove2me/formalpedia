-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredLoopAllocation.drift_scale_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T03:51:29.147569+00:00
-- url     : https://prove2.me/submissions/dc6ea6de-6033-4527-ac95-b2c6e80777c2

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopAllocation
import Theorems.Thm_ThreeSum_WeightedGlobalConcreteProfile_Profile_F_gt_one


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredLoopAllocation
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalColoredLoopSetup
open WeightedGlobalArenaPrefixFootprints
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {κ : ℕ}
namespace ThreeSum.WeightedGlobalColoredLoopAllocation
theorem _root_.solution (P : Profile κ) : 1≤P.drift*P.scale := by
  have hF:=P.F_gt_one
  have hM:=P.M_gt_one
  have hR : 0<WeightedGlobalGoodOutputCatalog.Rbar P.m := by
    unfold WeightedGlobalGoodOutputCatalog.Rbar
    positivity
  have hs : 0<P.scale := by unfold Profile.scale;positivity
  have hd : 0<P.drift := by unfold Profile.drift;positivity
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
end ThreeSum.WeightedGlobalColoredLoopAllocation
