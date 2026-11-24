-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.fou_mul_fouInv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:34.813234+00:00
-- url     : https://prove2.me/submissions/fc99ac44-1b76-4fc0-9cbf-d826bcba3295

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
theorem _root_.solution : fou l * fouInv l = 1 := by
  ext1 f
  rw [ContinuousLinearMap.mul_apply, fou_apply, fouInv_apply, FourierTransform.fourier_fourierInv_eq]
  rfl
end PositivityTheory.ThKR.LL
