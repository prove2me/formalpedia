-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:25:50.545374+00:00
-- url     : https://prove2.me/submissions/9f09326f-8700-4799-9cf2-7e021bdf6571

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
theorem _root_.solution (g : G l) : Mem (Subtype.val (p := (· ∈ sub l)) g) := Subtype.property (p := (· ∈ sub l)) g
end PositivityTheory.ThKR.Mp
