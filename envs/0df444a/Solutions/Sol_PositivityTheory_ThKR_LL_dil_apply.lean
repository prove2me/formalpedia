-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.dil_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:37:56.790612+00:00
-- url     : https://prove2.me/submissions/211d46ac-655f-49c7-ab00-774035e435a7

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
theorem _root_.solution {B : Eu l →L[ℝ] Eu l} (h : IsUnit B) (f : Sch l) (x : Eu l) : dil B f x = f (B x) := by
  rw [dil, dif_pos h]
  rfl
end PositivityTheory.ThKR.LL
