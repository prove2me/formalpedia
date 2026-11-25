-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.MpA.om_cont2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:43:25.638554+00:00
-- url     : https://prove2.me/submissions/315c5c04-de7b-42ac-8b91-a6fbacc3e099

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousTo
import Theorems.Thm_GroundTheory_Global_gaussianSchwartz_apply
import Theorems.Thm_PositivityTheory_ThKR_Mp_continuous_om
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
theorem _root_.solution : Continuous fun p : G l × L2 l => om p.1 p.2 := by
  refine continuous_iff_continuousAt.2 fun q => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Continuous fun p : G l × L2 l => ‖p.2 - q.2‖ + ‖om p.1 q.2 - om q.1 q.2‖ :=
    (continuous_snd.sub continuous_const).norm.add (((continuous_om q.2).comp continuous_fst).sub continuous_const).norm
  have h2 := h1.tendsto q
  simp only [sub_self, norm_zero, add_zero] at h2
  refine squeeze_zero (fun _ => norm_nonneg _) (fun p => ?_) h2
  calc ‖om p.1 p.2 - om q.1 q.2‖ = ‖(om p.1 p.2 - om p.1 q.2) + (om p.1 q.2 - om q.1 q.2)‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ ‖om p.1 p.2 - om p.1 q.2‖ + ‖om p.1 q.2 - om q.1 q.2‖ := norm_add_le _ _
    _ = ‖p.2 - q.2‖ + ‖om p.1 q.2 - om q.1 q.2‖ := by rw [← map_sub, LinearIsometryEquiv.norm_map]
end PositivityTheory.ThKR.Mp.MpA
