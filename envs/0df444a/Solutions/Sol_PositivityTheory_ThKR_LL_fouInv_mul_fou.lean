-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.fouInv_mul_fou
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:36.246853+00:00
-- url     : https://prove2.me/submissions/9744ce40-9216-4989-8e5b-9d8fb2a6cd11

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_HasDerivAtSchwartzToL2
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral
import Theorems.Thm_PositivityTheory_ThKR_LL_fou_apply
import Theorems.Thm_PositivityTheory_ThKR_LL_fouInv_apply

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
theorem _root_.solution : fouInv l * fou l = 1 := by
  ext1 f
  rw [ContinuousLinearMap.mul_apply, fou_apply, fouInv_apply, FourierTransform.fourierInv_fourier_eq]
  rfl
end PositivityTheory.ThKR.LL
