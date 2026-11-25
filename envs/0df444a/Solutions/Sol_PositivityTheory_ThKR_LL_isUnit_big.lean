-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.isUnit_big
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:21:21.314461+00:00
-- url     : https://prove2.me/submissions/a80135d2-baf9-49ac-bec1-341ffcd48dc9

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_HasDerivAtSchwartzToL2
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral
import Theorems.Thm_PositivityTheory_ThKR_LL_Intw_mul
import Theorems.Thm_PositivityTheory_ThKR_LL_Iso_mul
import Theorems.Thm_PositivityTheory_ThKR_LL_isUnit_ph
import Theorems.Thm_PositivityTheory_ThKR_LL_isUnit_dil
import Theorems.Thm_PositivityTheory_ThKR_LL_isUnit_fou
import Theorems.Thm_PositivityTheory_ThKR_LL_isUnit_fouInv
import Theorems.Thm_PositivityTheory_ThKR_LL_LD_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l]
namespace PositivityTheory.ThKR.LL
theorem _root_.solution {Ai : Eu l →L[ℝ] Eu l} (h : IsUnit Ai) (B C : Eu l →L[ℝ] Eu l) {c : ℝ} (hc : c ≠ 0) :
    IsUnit (big Ai B C c) := by
  refine (isUnit_ph _).mul (IsUnit.mul ?_ (isUnit_fou.mul ((isUnit_ph _).mul isUnit_fouInv)))
  rw [Algebra.smul_def]
  exact ((IsUnit.mk0 (c : ℂ) (by simpa using hc)).map _).mul (isUnit_dil h)
end PositivityTheory.ThKR.LL
