-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.ph_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:03:11.130749+00:00
-- url     : https://prove2.me/submissions/7d7be7de-8430-4e66-a557-561fc4e6c2d1

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_HasDerivAtSchwartzToL2
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral
import Theorems.Thm_PositivityTheory_ThKR_LL_ph_apply

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
theorem _root_.solution (S T : Eu l →L[ℝ] Eu l) : ph S * ph T = ph (S + T) := by
  ext f x
  simp only [ContinuousLinearMap.mul_apply, ph_apply, ← mul_assoc, ← Complex.exp_add, ContinuousLinearMap.add_apply,
    inner_add_right]
  congr 2
  push_cast
  ring
end PositivityTheory.ThKR.LL
