-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.continuous_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:29:39.463552+00:00
-- url     : https://prove2.me/submissions/cd78e1ea-1619-4acc-b1b8-c58ffa190083

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_LocalLift
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair

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
theorem _root_.solution : Continuous fun g : G l => ((pr g, fun f => om g f) : Sp l × (L2 l → L2 l)) :=
  continuous_induced_dom
end PositivityTheory.ThKR.Mp
