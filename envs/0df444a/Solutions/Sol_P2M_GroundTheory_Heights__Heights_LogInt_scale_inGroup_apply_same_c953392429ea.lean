-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_scale_inGroup_apply_same_c953392429ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:03:38.105708+00:00
-- url     : https://prove2.me/submissions/b6365a33-2192-4482-bf14-9cd1004ed80d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere

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
open MeasureTheory Set MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {n k : ℕ}
namespace GroundTheory.Heights₂.Heights.LogInt
theorem _root_.solution (i : Fin k) (c : ℂ) (u : Fin k × Fin n → ℂ) (j : Fin n) :
    scaleP (inGroup i) c u (i, j) = c * u (i, j) := by
  simp [scaleP, inGroup]
end GroundTheory.Heights₂.Heights.LogInt
