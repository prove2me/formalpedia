-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.temperate_quad
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:59.803035+00:00
-- url     : https://prove2.me/submissions/b3fa95e6-697f-478c-b737-44191b71ed57

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_HasDerivAtSchwartzToL2
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral

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
theorem _root_.solution (S : Eu l →L[ℝ] Eu l) : Function.HasTemperateGrowth fun x : Eu l => ⟪x, S x⟫ :=
  (innerSL ℝ).bilinear_hasTemperateGrowth Function.HasTemperateGrowth.id' S.hasTemperateGrowth
end PositivityTheory.ThKR.LL
