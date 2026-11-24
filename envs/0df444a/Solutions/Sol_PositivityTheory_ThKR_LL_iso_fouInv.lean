-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.iso_fouInv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:31.183183+00:00
-- url     : https://prove2.me/submissions/ed787163-405e-4614-8e4e-fc9b70cdec90

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_HasDerivAtSchwartzToL2
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral
import Theorems.Thm_PositivityTheory_ThKR_LL_fou_mul_fouInv
import Theorems.Thm_PositivityTheory_ThKR_LL_iso_fou

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
theorem _root_.solution : Iso (fouInv l) := fun f => by
  rw [← iso_fou (fouInv l f), ← ContinuousLinearMap.mul_apply, fou_mul_fouInv, ContinuousLinearMap.one_apply]
end PositivityTheory.ThKR.LL
