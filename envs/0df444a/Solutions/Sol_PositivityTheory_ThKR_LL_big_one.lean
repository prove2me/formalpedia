-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.big_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:52.135259+00:00
-- url     : https://prove2.me/submissions/00a7754e-ba42-4c95-8ac3-62594db1aeff

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_HasDerivAtSchwartzToL2
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral
import Theorems.Thm_PositivityTheory_ThKR_LL_ph_zero
import Theorems.Thm_PositivityTheory_ThKR_LL_dil_one
import Theorems.Thm_PositivityTheory_ThKR_LL_fou_mul_fouInv

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
theorem _root_.solution : big (1 : Eu l →L[ℝ] Eu l) 0 0 1 = 1 := by
  simp [big, ph_zero, dil_one, fou_mul_fouInv]
end PositivityTheory.ThKR.LL
