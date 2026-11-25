-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.isUnit_ph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:13:33.173793+00:00
-- url     : https://prove2.me/submissions/8f04f950-f04a-4841-82cc-cc7e5c6f8e6f

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_HasDerivAtSchwartzToL2
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral
import Theorems.Thm_PositivityTheory_ThKR_LL_ph_mul
import Theorems.Thm_PositivityTheory_ThKR_LL_ph_zero

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
theorem _root_.solution (S : Eu l →L[ℝ] Eu l) : IsUnit (ph S) :=
  ⟨⟨ph S, ph (-S), by rw [ph_mul, add_neg_cancel, ph_zero], by rw [ph_mul, neg_add_cancel, ph_zero]⟩, rfl⟩
end PositivityTheory.ThKR.LL
