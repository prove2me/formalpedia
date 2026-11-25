-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.isUnit_UU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:31:47.734048+00:00
-- url     : https://prove2.me/submissions/328ac0fa-ce91-4b08-9a71-e4e74a2ada3c

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MetaplecticUnipotentBlockSecondDiag
import Theorems.Thm_PositivityTheory_ThKR_LL_Intw_mul
import Theorems.Thm_PositivityTheory_ThKR_LL_Iso_mul
import Theorems.Thm_PositivityTheory_ThKR_LL_LD_mul
import Theorems.Thm_PositivityTheory_ThKR_LL_isUnit_fou
import Theorems.Thm_PositivityTheory_ThKR_LL_isUnit_fouInv
import Theorems.Thm_PositivityTheory_ThKR_LL_isUnit_ph


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
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
namespace PositivityTheory.ThKR.Mp
theorem _root_.solution (S : Matrix l l ℝ) (t : ℝ) : IsUnit (UU S t) :=
  isUnit_fou.mul ((isUnit_ph _).mul isUnit_fouInv)
end PositivityTheory.ThKR.Mp
