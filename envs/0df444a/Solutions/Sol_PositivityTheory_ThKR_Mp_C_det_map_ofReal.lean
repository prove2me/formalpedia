-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.C.det_map_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:32:29.621411+00:00
-- url     : https://prove2.me/submissions/419c05cf-8505-46fe-9477-aff924d67f9c

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MapOfRealMul

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
open scoped Real
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open PositivityTheory.ThKR.Mp.C
namespace PositivityTheory.ThKR.Mp.C
theorem _root_.solution (M : Matrix l l ℝ) : (M.map Complex.ofReal).det = (M.det : ℂ) :=
  (RingHom.map_det Complex.ofRealHom M).symm
end PositivityTheory.ThKR.Mp.C
