-- Prove2me | solution 1 for PositivityTheory.ThKEst.LinDerPf.pr_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:36.205341+00:00
-- url     : https://prove2.me/submissions/40690757-cf90-49b8-97bc-07c647eff125

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_LinDerA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.LinDerPf
open Filter Topology Asymptotics
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
namespace PositivityTheory.ThKEst.LinDerPf
theorem _root_.solution (a : A →L[ℝ] A) (x : A) : pr a x = (1 / 2 : ℝ) • (x - a x) := rfl
end PositivityTheory.ThKEst.LinDerPf
