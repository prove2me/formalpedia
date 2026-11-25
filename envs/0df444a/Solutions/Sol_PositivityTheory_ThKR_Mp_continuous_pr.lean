-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.continuous_pr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:41:43.851657+00:00
-- url     : https://prove2.me/submissions/e43b4242-c59e-4596-9298-204d3195c819

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_LocalLift
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Theorems.Thm_PositivityTheory_ThKR_Mp_continuous_pair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL
open scoped Real ContDiff
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable (l : Type) [Fintype l] [DecidableEq l]
variable {l}
namespace PositivityTheory.ThKR.Mp
theorem _root_.solution : Continuous (pr : G l → Sp l) := by
  have h := (continuous_pair (l := l)).fst
  exact h
end PositivityTheory.ThKR.Mp
