-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.isUnit_fouInv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:41.95735+00:00
-- url     : https://prove2.me/submissions/79063005-bd7d-4ec2-8034-6acf8eb29244

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_HasDerivAtSchwartzToL2
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral
import Theorems.Thm_PositivityTheory_ThKR_LL_fou_mul_fouInv
import Theorems.Thm_PositivityTheory_ThKR_LL_fouInv_mul_fou

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
theorem _root_.solution : IsUnit (fouInv l) := ⟨⟨_, _, fouInv_mul_fou, fou_mul_fouInv⟩, rfl⟩
end PositivityTheory.ThKR.LL
