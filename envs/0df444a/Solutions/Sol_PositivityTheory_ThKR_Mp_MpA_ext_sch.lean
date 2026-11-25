-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.MpA.ext_sch
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:32:31.228801+00:00
-- url     : https://prove2.me/submissions/cf4cf2e9-41de-4284-9a53-137dc75de39b

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousTo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL LineDeriv
open scoped Real ContDiff
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open PositivityTheory.ThKR.Mp.MpA
namespace PositivityTheory.ThKR.Mp.MpA
theorem _root_.solution (V : (Sch l →L[ℂ] Sch l)ˣ) (hn : ∀ f, ‖schwartzToL2 l (V.1 f)‖ = ‖schwartzToL2 l f‖) (f : Sch l) :
    ext V hn (schwartzToL2 l f) = schwartzToL2 l (V.1 f) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ f
end PositivityTheory.ThKR.Mp.MpA
