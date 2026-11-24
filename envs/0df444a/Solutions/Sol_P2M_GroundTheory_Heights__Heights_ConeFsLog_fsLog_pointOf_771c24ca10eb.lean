-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeFsLog_fsLog_pointOf_771c24ca10eb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:32.387896+00:00
-- url     : https://prove2.me/submissions/9e785e54-df47-4446-bf0a-7d0dcabd3b67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ConeBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSlab
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeFsLogIntegrable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFsLog_dualNorm_pointOf_510e3d6db40f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Set Matrix Filter
noncomputable section
open GroundTheory.Heights₂.Heights.ConeFsLog
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ConeFsLog
theorem _root_.solution (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    fsLog h u (h.pointOf y) = Real.log (‖∑ j, u j * h.pointOf y j‖ / ‖y‖) := by
  rw [fsLog, dualNorm_pointOf]
end GroundTheory.Heights₂.Heights.ConeFsLog
