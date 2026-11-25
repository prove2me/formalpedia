-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.MpA.dd_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:32:28.423919+00:00
-- url     : https://prove2.me/submissions/18969f1f-90f8-4706-abf6-8249f0ec1882

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousTo
import Theorems.Thm_GroundTheory_Global_gaussianSchwartz_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.gaussianSchwartz_apply



set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL LineDeriv
open scoped Real ContDiff
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open PositivityTheory.ThKR.Mp.MpA
namespace PositivityTheory.ThKR.Mp.MpA
theorem _root_.solution : dd (1 : Mat l) = 1 := by
  have h : upperParabolic (1 : Mat l) = 1 := by
    ext a b
    by_cases hab : a = b <;> simp [upperParabolic, Matrix.one_apply, hab]
  rw [dd, h, det_one]
end PositivityTheory.ThKR.Mp.MpA
