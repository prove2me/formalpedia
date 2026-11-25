-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.om_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:33:57.811053+00:00
-- url     : https://prove2.me/submissions/dd1085ee-39ec-4bc1-9916-cce9adc6a69a

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
theorem _root_.solution (g : G l) (w : l ⊕ l → ℝ) (f : L2 l) : om g (rho w f) = rho ((pr g).1 *ᵥ w) (om g f) := (mem g).rho w f
end PositivityTheory.ThKR.Mp
