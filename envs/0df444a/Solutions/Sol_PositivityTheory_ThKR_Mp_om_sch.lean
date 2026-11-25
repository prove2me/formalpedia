-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.om_sch
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:34:02.77043+00:00
-- url     : https://prove2.me/submissions/418fefbb-c604-425a-b2a1-109c2155b2ed

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_LocalLift
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Theorems.Thm_PositivityTheory_ThKR_Mp_mem

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
theorem _root_.solution (g : G l) (f : Sch l) : om g (schwartzToL2 l f) = schwartzToL2 l (omS g f) := (mem g).compat f
end PositivityTheory.ThKR.Mp
